import { simpleGit } from 'simple-git';
import fs from 'fs/promises';
import path from 'path';
import os from 'os';

const SOURCE_REPO = 'https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify.git';

// Get the repo root (directory containing package.json)
const REPO_ROOT = path.resolve(import.meta.dirname, '..');

// Files/folders that belong to this generator (should never be deleted)
const KEEP_PATTERNS = [
  '.git',
  '.github',
  '.gitignore',
  '.lake',
  'node_modules',
  'package.json',
  'package-lock.json',
  'README.md',
  'scripts',
];

// Files/folders to remove from the cloned source repo
const REMOVE_PATTERNS = [
  '.git',
  '.github',
  '.gitignore',
  '.claude',
  '.cargo',
  '.envrc',
  '.logs',
  '.tmp',
  '.typos.toml',
  '.vscode',
  'aeneas',
  'aeneas-toolchain',
  'aeneas-tweaks.txt',
  'ai-benchmark',
  'Cargo.lock',
  'Cargo.toml',
  'CONTRIBUTING.md',
  'curve25519-dalek',
  'curve25519_dalek.llbc',
  'deps.json',
  'extract-functions.txt',
  'functions.json',
  'LICENSE-APACHE',
  'LICENSE-MIT',
  'node_modules',
  'package.json',
  'package-lock.json',
  'README.md',
  'scripts',
  'shell.nix',
  'site',
  'src-modifications.diff',
  'status.csv',
  'target',
];

/**
 * Clean the repo root by removing everything except matching KEEP_PATTERNS
 */
async function cleanRepoRoot() {
  console.log('Cleaning repo root (preserving generator files)...');

  const entries = await fs.readdir(REPO_ROOT);

  for (const entry of entries) {
    if (!KEEP_PATTERNS.includes(entry)) {
      const fullPath = path.join(REPO_ROOT, entry);
      console.log(`  Removing: ${entry}`);
      await fs.rm(fullPath, { recursive: true, force: true });
    }
  }

  console.log('Repo root cleaned.');
}

/**
 * Clone the source repository to a temp directory
 * Returns { tempDir, commitHash }
 */
async function cloneRepo() {
  const tempDir = await fs.mkdtemp(path.join(os.tmpdir(), 'curve25519-clone-'));

  console.log(`Cloning ${SOURCE_REPO} to ${tempDir}...`);
  const git = simpleGit();
  await git.clone(SOURCE_REPO, tempDir, ['--depth', '1']);
  console.log('Clone complete.');

  // Get the commit hash of the cloned repo
  const clonedGit = simpleGit(tempDir);
  const log = await clonedGit.log(['-1']);
  const commitHash = log.latest.hash;
  console.log(`Source commit: ${commitHash}`);

  return { tempDir, commitHash };
}

/**
 * Remove files/folders matching REMOVE_PATTERNS from the cloned repo
 */
async function stripClonedRepo(cloneDir) {
  console.log('Stripping unwanted files from cloned repo...');

  for (const pattern of REMOVE_PATTERNS) {
    const fullPath = path.join(cloneDir, pattern);
    try {
      await fs.rm(fullPath, { recursive: true, force: true });
      console.log(`  Removed: ${pattern}`);
    } catch (e) {
      // File doesn't exist, that's fine
    }
  }

  console.log('Strip complete.');
}

/**
 * Copy stripped files from temp dir to repo root
 */
async function copyToRepoRoot(sourceDir) {
  console.log('Copying files to repo root...');

  const entries = await fs.readdir(sourceDir);

  for (const entry of entries) {
    const src = path.join(sourceDir, entry);
    const dest = path.join(REPO_ROOT, entry);
    await fs.cp(src, dest, { recursive: true });
    console.log(`  Copied: ${entry}`);
  }

  console.log('Copy complete.');
}

/**
 * Find all .lean files recursively
 */
async function findLeanFiles(dir, files = []) {
  const entries = await fs.readdir(dir, { withFileTypes: true });

  for (const entry of entries) {
    const fullPath = path.join(dir, entry.name);

    if (entry.isDirectory()) {
      await findLeanFiles(fullPath, files);
    } else if (entry.name.endsWith('.lean')) {
      files.push(fullPath);
    }
  }

  return files;
}

/**
 * Process a single Lean file:
 * - Find BEGIN TASK / END TASK markers
 * - Remove content between them
 * - Add `sorry` with matching indentation
 * - Return task count
 */
async function processLeanFile(filePath) {
  const content = await fs.readFile(filePath, 'utf-8');
  const lines = content.split('\n');

  const resultLines = [];
  let inTask = false;
  let taskCount = 0;
  let taskStartLine = -1;

  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    const lineNum = i + 1; // 1-indexed for error messages

    if (line.includes('BEGIN TASK')) {
      if (inTask) {
        throw new Error(`${filePath}:${lineNum}: Found BEGIN TASK while already inside a task block (started at line ${taskStartLine})`);
      }
      inTask = true;
      taskCount++;
      taskStartLine = lineNum;
      resultLines.push(line); // Keep the BEGIN TASK line

      // Create indentation to align sorry with where -- BEGIN TASK starts
      const dashIndex = line.indexOf('--');
      const indent = ' '.repeat(dashIndex);
      resultLines.push(indent + 'sorry');
    } else if (line.includes('END TASK')) {
      if (!inTask) {
        throw new Error(`${filePath}:${lineNum}: Found END TASK without matching BEGIN TASK`);
      }
      inTask = false;
      resultLines.push(line); // Keep the END TASK line
    } else if (!inTask) {
      resultLines.push(line);
    }
    // Lines inside task blocks are skipped
  }

  // Check for unclosed task block
  if (inTask) {
    throw new Error(`${filePath}: Unclosed task block (BEGIN TASK at line ${taskStartLine} has no matching END TASK)`);
  }

  // Only write back if there were tasks
  if (taskCount > 0) {
    await fs.writeFile(filePath, resultLines.join('\n'));
  }

  return taskCount;
}

/**
 * Process all Lean files and generate task manifest
 */
async function processLeanFiles(targetDir) {
  console.log('Processing Lean files...');

  const leanFiles = await findLeanFiles(targetDir);
  const tasksManifest = [];
  let totalTasks = 0;

  for (const filePath of leanFiles) {
    const relativePath = path.relative(targetDir, filePath);
    const taskCount = await processLeanFile(filePath);

    if (taskCount > 0) {
      console.log(`  ${relativePath}: ${taskCount} task(s)`);
      tasksManifest.push({
        file: relativePath,
        tasks: taskCount
      });
      totalTasks += taskCount;
    }
  }

  console.log(`\nTotal: ${tasksManifest.length} files with ${totalTasks} tasks`);

  return tasksManifest;
}

/**
 * Write the tasks manifest
 */
async function writeManifest(manifest, commitHash) {
  const manifestPath = path.join(REPO_ROOT, 'tasks-manifest.json');

  const output = {
    sourceCommit: commitHash,
    summary: {
      totalFiles: manifest.length,
      totalTasks: manifest.reduce((sum, f) => sum + f.tasks, 0)
    },
    files: manifest
  };

  await fs.writeFile(manifestPath, JSON.stringify(output, null, 2));
  console.log(`\nManifest written to: ${manifestPath}`);
}

/**
 * Main entry point
 */
async function main() {
  try {
    // Step 1: Clean repo root (remove previous output, keep generator files)
    await cleanRepoRoot();

    // Step 2: Clone source repo to temp directory
    const { tempDir, commitHash } = await cloneRepo();

    // Step 3: Strip unwanted files from clone
    await stripClonedRepo(tempDir);

    // Step 4: Copy remaining files to repo root
    await copyToRepoRoot(tempDir);

    // Step 5: Process Lean files (extract tasks)
    const manifest = await processLeanFiles(REPO_ROOT);

    // Step 6: Write manifest
    await writeManifest(manifest, commitHash);

    // Step 7: Cleanup temp directory
    await fs.rm(tempDir, { recursive: true, force: true });
    console.log('Cleaned up temp directory.');

    console.log('\nDone!');
  } catch (error) {
    console.error('Error:', error);
    process.exit(1);
  }
}

main();

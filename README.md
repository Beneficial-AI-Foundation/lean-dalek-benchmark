# Curve25519 Lean Benchmark

This repo contains a benchmark dataset derived from [curve25519-dalek-lean-verify](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify) by removing the proofs of verification tasks. The file `tasks-manifest.json` contains a list of tasks in the form of a list of files with a count of the number of `sorry` in each file which needs to be replaced with a proof. Each of these tasks is known to be well-formed in the sense it is known that a proof exists. 

**The challenge is:** For each of the files listed in `tasks-manifest.json`, remove each `sorry` and replace that line with a valid proof. No other lines of the file may be removed. Any `sorry` replaced with a valid proof is a partial success, every `sorry` in a file replaced with a valid proof is a complete success for that file. 

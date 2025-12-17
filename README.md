# Curve25519 Benchmark Generator

This repo contains a benchmark dataset derived from [curve25519-dalek-lean-verify](https://github.com/AeneasVerif/curve25519-dalek-lean-verify) by removing the proofs of verification tasks. The file `tasks-manifest.json` contains a list of tasks in the form of a list of files with a count of the number of `sorry` in each file which needs to be replaced with a proof.

**The challenge is:** For each of the files listed in `tasks-manifest.json`, remove each `sorry` and replace that lines with a proof of that specific goal. No other lines of the file may be removed. Any `sorry` replaced with a valid proof is a success, all every `sorry` replace with a valid proof is a completion of that file. 

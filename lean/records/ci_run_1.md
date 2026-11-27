<!-- AQIDA_CONSTITUTIONAL_SCOPE: gate | CLAIM_BOUNDARY: record of one automated run; it shows that the files build and pass their own checks on a fresh machine, nothing more | FALSIFICATION_TESTS: re-run the workflow (Actions tab, "Run workflow") and compare -->

# First clean-machine run (GitHub Actions)

- Repository: https://github.com/aqida-ai/tr26-151-problem1 (private at the time of the run).
- Workflow: `.github/workflows/lean_verify.yml`, run 1, triggered by the push of the workflow file itself.
- Run: https://github.com/aqida-ai/tr26-151-problem1/actions/runs/45996650118
- Commit: `75923289df87b4680e4ef15e5d3030017986b1b0`. Date: 27 November 2026 (about 12:15 UTC).
- Runner: `ubuntu-latest` (GitHub-hosted). Status: success. Total duration: 4 min 0 s.

| step | result | duration |
|---|---|---|
| Checkout | success | 1 s |
| Install elan (Lean toolchain manager) | success | under 1 s |
| Fetch the Mathlib cache (`lake exe cache get`; this also installs Lean 4.30.0-rc2 and clones the pinned dependencies) | success | 2 min 13 s |
| Build TheoremL and TheoremL_LayerRanks (`lake build`) | success | 43 s |
| Axiom check (`bash check_axioms.sh`) | success | 32 s |
| Set up Python 3.12 | success | under 1 s |
| Verify the seven certificates (`python certificates/verify_certificates.py`) | success | 24 s |

What the job log shows (the raw log of the job, 518 lines, was read on 27 November 2026):

- `lake build` printed 27 lines of the form "depends on axioms: [propext, Classical.choice, Quot.sound]"
  (10 from `TheoremL.lean`, 17 from `TheoremL_LayerRanks.lean`) and "Build completed successfully".
- The axiom check printed the same 27 lines again, one line with `sorryAx` (the planted `sorry` of
  `NegativeControl.lean`), "negative control: sorryAx reported, as expected" and "check_axioms.sh: PASS".
  No line of the log names any other axiom, and no line contains FAIL.
- The certificate verifier printed "certificate PASS" for t = 10, ..., 16 with integer bounds
  11, 14, 16, 17, 19, 21, 23 and "OVERALL: ALL SEVEN CERTIFICATES PASS".
- One warning from GitHub: the actions `actions/checkout@v4` and `actions/setup-python@v5` target Node.js 20,
  which GitHub now runs on Node.js 24. It does not affect the checks.

What this run does not show: it is the same Lean kernel and the same Mathlib as on the authoring machine (the
Mathlib binaries were downloaded from the Mathlib cache, not rebuilt); no proof checker other than Lean was used;
no human mathematician has read the proofs. The files were uploaded through the GitHub web interface, so the
bytes are those of the authoring machine (hashes in `MANIFEST.md`).

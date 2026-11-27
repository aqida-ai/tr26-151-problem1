<!-- AQIDA_CONSTITUTIONAL_SCOPE: gate | CLAIM_BOUNDARY: release packaging of already recorded results; states nothing new | FALSIFICATION_TESTS: lake build, check_axioms.sh, verify_certificates.py -->

# MANIFEST

Every file of this package except `MANIFEST.md` itself (a file cannot contain its own hash), with its
SHA-256 and its size in bytes. Produced on 2026-11-26 in Git Bash, from the package root, by:

```bash
find . -type f ! -name MANIFEST.md | LC_ALL=C sort | while read f; do
  printf '%s  %8d  %s\n' "$(sha256sum "$f" | cut -d' ' -f1)" "$(stat -c %s "$f")" "${f#./}"
done
```

Output (verbatim; columns: SHA-256, size in bytes, path):

```text
e66c9a3e1b340d95937f5559178f225dc88bc6fe9324a7d3f48f74d6f4e7c2b4      1637  .github/workflows/lean_verify.yml
67c202c7a2e14c7c8a0388307a4c3272cc8de84241b469d13b6c010f2010c554      1568  CITATION.cff
5fbdef8c8ba9bca061eb05c4ef84a13891f7cabfdceb29cba167fd0d6cbaf8da      1073  LICENSE
88b2265c5327296ebce6a56e264e5e9332cd1b1eec5c1bb5a77f061f8dd2cb88       994  LICENSE-PAPER.md
218b6ad8d3cdcbf9867bd2af51e489bc3e89ca7b0c345592b2575ca108a6f5ac      9538  README.md
c92141f1ec33811fe2d9d413045aa955713354c00804bf8ff12f1758806fce5e      5218  certificates/three_point_cert_t10_proj.json
5a6176d4197c7893caf8c12868a2707e6a556b55e075fdb448e64b4cac9f0856      5793  certificates/three_point_cert_t11_proj.json
9629ed25e93f9f62c785b76cd6ee5d5f94fd3b641abefa73692052f2ef1d59c2      7924  certificates/three_point_cert_t12_proj.json
c66ba6302b6938ac17176afaff0b54dd2267e1b02de3b28a3ac9a223cb62e9d5      9265  certificates/three_point_cert_t13_proj.json
f5e41cc5168190789dcaf0cd7d7a9c55c32440b9aa7324d911d9164504ba73d2     11611  certificates/three_point_cert_t14_proj.json
63280e942dc30bf42f5a3721f18fca8f2d9458a1029c8fed25657bae588f95e5     12963  certificates/three_point_cert_t15_proj.json
c5ef4be603fb72104ec6232f514926ab9eb24467e2c1c3ce36fef09d503bc915     15848  certificates/three_point_cert_t16_proj.json
ca75275cf4dfc1877fd3d4e17091a02a1e67cdefe8907725bc2e8773198d6e18     10886  certificates/verify_certificates.py
3663e64bd28ac57541937af06290bfcb603b831e7c0f3894e1c853f06bbb4748     14665  certificates/verify_output.txt
875d72d4ab36dcc423a99b366066fc6cad037c9641bb9a06008bf5907d2f2a63      1767  lean/NegativeControl.lean
67c6f07984c036f9462704851ea91831822356062a8a32612997542e4dcad190      1071  lean/SHA256SUMS.txt
3019bee14ed972d72cf0759bc36aca2c096a9d742649efff15afcbf06b3cef92     49218  lean/TheoremL.lean
a1b16696a0fbef1aec580a126b5a9bd3ca6c0066129296af9e26c32c21adeefd     64096  lean/TheoremL_LayerRanks.lean
587ab20d2bda1e316cc86444253a522c81960c4a4d4218535a9eb88315c77cd9      2716  lean/check_axioms.sh
a33bc633258162d71b7e7aeff668697b0d644092ac3e8918a6607d53ede0375e       972  lean/lakefile.toml
ce4c4e3d87434b9663f46de25ce34b48a0cf0d392e0a320a0787b4674a2d7b61        29  lean/lean-toolchain
78026fdb082bb26f0a23148191ed08c18308b2ee94c165511f05d74f941876d4    497439  paper/PAPER_TR26_151_PROBLEM1.pdf
d9fa58f867b594b54a30f355f28c124f8fcfa7f876b701858191bd80aadea191     25463  paper/PAPER_TR26_151_PROBLEM1.tex
ff6d909090cc47f33fdc3afd4e94d0b4488bc7ed47d8cd04e113b1c350c7c001       800  paper/PAPER_TR26_151_PROBLEM1_audit.tex
edbf5891cfb124f6726adb3a4203137aae8b09753db708182f1820f0a6d415b7      1404  paper/PAPER_TR26_151_PROBLEM1_bib.tex
a7f75253fa939f043e6e20ff6256242f3b8c1532f7cf6e7dcec802864168b83d      5260  paper/PAPER_TR26_151_PROBLEM1_lean.tex
ec1b1e3abd09f2a46e0b93f26298d87789f06a5d6db4531214f5ee68115a739c      5300  paper/PAPER_TR26_151_PROBLEM1_lit.tex
```

27 files listed.

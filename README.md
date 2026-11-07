# melete-math

This repository holds the machine checks behind nonexistence results on directed strongly regular graphs (DSRGs): the programs, the graph catalogues they use as controls, the SAT certificates and the Lean modules. Each directory belongs to one paper and can be checked on its own.

| Directory | Paper | What it checks |
|---|---|---|
| [`dsrg-rank-method/`](dsrg-rank-method/README.md) | Nonexistence of DSRGs with ten parameter sets: the rank of A − θI versus a submatrix prescribed at a vertex | every machine step of the proofs for (50, 11, 7, 0, 3), (68, 13, 7, 0, 3), (100, 16, 7, 0, 3), (108, 19, 9, 0, 4), (48, 9, 5, 0, 2), (55, 16, 12, 1, 6), (66, 10, 5, 4, 1), (91, 12, 6, 5, 1), (96, 15, 10, 9, 1) and (28, 6, 3, 2, 1) |

The README of a directory lists its requirements, every command with its expected exit code and last line of output, and what the checks do not cover. The commands run from that directory.

## Integrity

`MANIFEST.sha256` lists the SHA-256 of every file of the repository, one line per file in the format of `sha256sum`, so a copy can be checked with

```sh
sha256sum -c MANIFEST.sha256
```

Proof files too large to store are not in the repository; the `certificates.json` of a directory gives the command that recreates each of them and the SHA-256 of the result.

Every push and a weekly run scan the whole history for leaked credentials with two independent scanners, gitleaks and TruffleHog (`.github/workflows/secret-scan.yml`).

## License and citation

The code is released under the MIT license (`LICENSE`); the data, the certificates and the texts under CC BY 4.0 (`LICENSE-DATA`). `CITATION.cff` gives the citation.

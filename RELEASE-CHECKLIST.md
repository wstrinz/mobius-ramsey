# Release checklist

This repository is a **release candidate**. Nothing has been published: no public repository,
tag, release, Zenodo deposit or Palomar submission exists. Every step in part B is the author's
alone, and each needs his explicit go. This file may be deleted in the commit that goes public.

## A. Release gates

| Gate | Status |
|---|---|
| **R1. The Lean package** | |
| R1a. Build: standard axioms only, no `sorry` outside `Challenge.lean` | done (local build, Linux and Windows) |
| R1b. Palomar's judge, `scripts/verify-comparator.sh` (Lean + NanoDa + con-ron, bubblewrap sandbox), local Linux run | done: "Your solution is okay!" |
| R1c. Negative controls refused for their expected reasons | done (5 of 5) |
| R1d. Fresh-runner CI (`.github/workflows/verify.yml`) | **open**: needs the public repository (step B1) |
| R1e. Fidelity review of the statements by an agent or person who did not write them | done (an AI agent that did not build the package: faithful, with fixes to prose, metadata and credit wording, all applied; item-by-item table in `docs/FIDELITY.md`) |
| R1f. Fresh reproduction from `REPRODUCE.md` by an agent or person who did not write them | done (an AI agent, from `README.md` and `REPRODUCE.md` alone: reproduced, every required step passed; the friction it found in the instructions is fixed) |
| **R2. Final prior-work search for Theorem C** (`docs/PRIOR-WORK-SEARCH.md`, "Still to do"): the remaining openai/math follow-up repositories, Kříž 1991 and 1992, MathOverflow, the Palomar registry, a v2 of arXiv:2609.23327 | **open** |
| **R3. Note text** | |
| R3a. OpenAI's Theorem 1.1 and Proposition 2.1 quoted verbatim (`note/check_verbatim.py`) | done |
| R3b. AI disclosure (`DISCLOSURE.md`, note §5) | drafted; the author to edit and confirm the exploration-thread model |
| R3c. A verification level on every claim of the note | done |
| R3d. Remaining `\TODO` / `\PH` markers in `note/mobius.tex`. Resolved: the Ratcliffe, Beardon and Ahlfors locations for `Möb(S^{d-1}) ≅ PO(1,d)` (`docs/CITATION-SOURCES.md`). Still open: Ahlfors's definition of `SO(n,1)` (only search snippets seen); the final prior-work search; a v2 of arXiv:2609.23327 on posting day; preferred citation forms for JD-Jones-ASES, Rogerhu12 and atimics; the exploration-thread model; release date, repository URL, DOI | **open** (partly done) |
| R3e. First LuaLaTeX build of the note (no TeX was available when it was drafted): glyph coverage of the Lean excerpts, overfull lines, length | **open** |
| **R4. The author reads the final text** (README, note, DISCLOSURE, formalization.yaml) | **open** |
| **R5. Outreach decision**: a courtesy note to JD-Jones-ASES (whose `hsuff` this line of work discharges) | **open**: the author's call |

## B. Steps only the author can take, in order

- [ ] **B1. Create the public repository** `mobius-ramsey` from this directory, at a commit C
  (after R1e, R1f, R2, R3 and R4). Then add `repository-code` to `CITATION.cff`, and let
  `.github/workflows/verify.yml` run on the fresh runner (gate R1d).
- [ ] **B2. Palomar mechanical check** of commit C: Palomar's own pipeline runs the same
  `lake comparator` with the same kernels on its own export. Points to confirm first:
  - the root licence is MIT, with the vendored OpenAI files under Apache-2.0
    (`LICENSES/Apache-2.0.txt`, `NOTICE`). Palomar detects only the root licence, so
    `project.license: MIT` is mechanically consistent, but PalomarTemplate's own CI requires
    Apache-2.0 and whether Palomar's editors accept a mixed tree is untested; the alternative is
    Apache-2.0 for the whole repository;
  - the submitter declares responsible authorship (only the author can);
  - the editorial review scores notability, and a 3 is a rejection without appeal.
- [ ] **B3. Zenodo.** Turn on the Zenodo GitHub integration for the repository, then make a GitHub
  release at commit C. `.zenodo.json` (kept identical to `CITATION.cff`) is read at that
  moment. The mint is effectively permanent: owner deletion is possible only within 30 days.
  Afterwards, add the DOI badge and the DOI in `README.md`, `CITATION.cff` and the note in a
  later commit.
- [ ] **B4. Palomar register decision**: submit commit C (or a later one) to the registry, or not.
  Registration is permanent.

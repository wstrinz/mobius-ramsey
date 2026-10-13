# Authorship, AI use and review

## Human author

**Will Strinz** is the sole human author and the person responsible for this repository. He
directed the work, made the decisions recorded here (scope, licence, what to release), read the
hand proof of Theorem C, and is accountable for the release. He is not an expert in Euclidean
Ramsey theory.

## AI contributions, by name

| Contributor | What it did |
|---|---|
| Claude Opus 5.5 (Anthropic), in claude.ai | The exploratory conversation in which Theorem C and its proof first appeared, and the task packet that started the project |
| **Claude Opus 5.5** (Anthropic) | Coordination of the work; the Lean proofs (`MobiusRamsey/`); the port of the development to the Lean module system; the exact certificates and probes used while exploring; the reviews listed below as AI reviews; drafting of the note and of this repository's documentation |
| **Claude Sonnet 5.5** (Anthropic) | The prior-work searches (`docs/PRIOR-WORK-SEARCH.md`); hygiene checks of the exploratory numerical probes; a fresh, from-the-README reproduction of an earlier Lean build of Theorem A (reproduced); a fresh reproduction of this package from `README.md` and `REPRODUCE.md` alone (reproduced, with friction in the instructions that has since been fixed) |

The agents worked in Claude Code. Every machine check reported in this repository was run by
these agents; the author did not re-run them.

## Foundation

**OpenAI's result 172**, *A classification of finite Euclidean Ramsey configurations*, and its
complete Lean proof (github.com/openai/math, commit `fd4aeeb2`), is the foundation of this work.
Theorem C is a short consequence of it, and the Lean proof here builds on OpenAI's Lean proof,
whose 28 files are included (Apache-2.0; see `NOTICE`).

## Review: who checked what

| Check | By | Kind |
|---|---|---|
| Lean proofs: kernel checking, axioms, statement match | Lean, NanoDa and con-ron kernels through `lake comparator` | machine |
| Hand proof of Theorem C, step by step | Claude Opus 5.5 (the coordinating agent) | AI review |
| Fidelity of the Theorem C and corollary statements to the mathematics (definitions, hypotheses, the Möbius model) | the Claude agents that wrote the Lean proofs (their own fidelity notes, in the module docstrings and `Challenge.lean`) | AI self-assessment |
| Fidelity of this package (the four advertised statements, the Möbius model, the note, the credit and the metadata), by an agent that did not build it | Claude Opus 5.5 | AI review: faithful, with fixes to prose, metadata and credit wording only; all fixes applied. The item-by-item table is `docs/FIDELITY.md` |
| Fresh reproduction of this package from `README.md` and `REPRODUCE.md` alone, by an agent that did not build it | Claude Sonnet 5.5 | AI reproduction: reproduced, every required step passed (about 24 minutes); the friction it found in the instructions was fixed in `REPRODUCE.md` and `docs/PORT-LOG.md` |
| Fidelity of an earlier Lean statement of Theorem A (`ramsey_of_algebraic`, same statement) | a Claude agent that did not build it | AI review |
| Hand proof of Theorem C, line by line | Will Strinz | owner's read: an author's sign-off by a non-expert, **not** expert review |
| The note (`note/mobius.tex`) | Claude agents; the author's final read before release | AI review; owner's read |

**No human expert has reviewed this work.** The identification of the maps `mobiusMap L`,
`L ∈ O(1,d)`, with the Möbius group of the sphere (for `d ≥ 2`) is classical and cited, not
formalized.

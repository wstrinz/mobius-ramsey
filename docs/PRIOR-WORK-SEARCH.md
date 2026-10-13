# Prior-work search log (Theorem C and its corollaries)

**Result: no prior statement of Theorem C was found** ("the Ramsey property of a finite spherical
set is invariant under Möbius transformations of the sphere"). This is a search result, not a
proof of novelty. The searches were made by AI agents (Claude models; see `DISCLOSURE.md`) on
2026-10-11 and 2026-10-12, in three rounds, and the headline findings were re-verified by a second
agent through the GitHub API. The search must be repeated immediately before release (see
"Still to do").

## Nearest work found

- **Pálvölgyi, arXiv:2609.23327 (v1, 2026-09-20), appendix §E.** Lemma A.5 proves that the
  *existence of his derivation certificates* is invariant under real Möbius maps, and states
  explicitly that the lemma "does not assert that the Ramsey property itself is Möbius invariant."
  Theorem A.7 has a Möbius-invariant hypothesis without stating invariance; Theorem A.10 is about
  certificates only. The appendix is labelled by its author as AI-generated and unchecked.
- **OpenAI, result 172** (github.com/openai/math at `fd4aeeb2`): the classification on which
  Theorem C rests. Its paper and Lean tree contain no occurrence of "Möbius", "conformal",
  "cross-ratio" or "projective".
- **Theorem A (algebraic coordinates ⇒ Ramsey), used for Corollary (c), is prior work:**
  - JD-Jones-ASES/six-concyclic-lean, root commit `0703d7d` (2026-10-07): Lean, criterion level;
    the Ramsey conclusions are conditional on a sufficiency hypothesis `hsuff`.
  - Rogerhu12/openai-math-extensions, commit `f8a2bb2` (2026-10-07): TeX, the same idempotent
    proof.
  - atimics/math2, commit `8ab51fa` (2026-10-08), `EndToEnd/AlgebraicRamsey.lean`: Lean, end to end
    and unconditional, for algebraic configurations with full affine span (its Lean statement
    carries a spanning hypothesis `hspan`); its written derivation extends this to sets similar
    to algebraic ones.
  - eliottcassidy2000/math (2026-10-07): an audit note restating it conditionally on result 172.

  This repository's `ramsey_of_algebraic` is a further Lean proof of Theorem A, not a first one.
- **Corollaries.** Three-point sets (all triangles are Ramsey: Frankl–Rödl 1986, and result 172's
  Cor. 7.4), Möbius images of regular polygons, and the `circ(k t)` / `circ(t + c)` families are
  derivable by an expert from Theorem C and known results. They are not claimed as independently
  new.

## What was searched

- **openai/math:** HEAD (still `fd4aeeb2` at the time), CONTENTS.md, every preprint TeX source, the
  Lean tree, the one merged PR, and an 83-fork comparison.
- **arXiv API** (export.arxiv.org), about 42 queries through 2026-10-12, sorted by date: Euclidean
  Ramsey with spherical / circle / transcendental / algebraic / Möbius / conformal / cross-ratio /
  tensor / field criterion; "not Ramsey"; Graham's spherical conjecture; author queries for
  Pálvölgyi. Recent relevant items (none states Theorem C): 2608.11736, 2608.09649, 2608.10865,
  2510.15677.
- **Palomar registry:** all 520 entries at the time, plus 23 full-text queries.
- **GitHub:** 166 repositories by README, 145 repositories related to the OpenAI release by code
  scan; repository searches for "euclidean ramsey" and "FieldCriterion".
- **Other:** MathOverflow and math.stackexchange; google-deepmind/formal-conjectures; the
  vibemathed AI-results catalogue; general web search; Leader–Russell–Walters (arXiv 1012.1350,
  1012.5468) and Graham's 1994 survey and Handbook chapter 11, which contain no Möbius, inversion,
  projective or cross-ratio remark.

## Posting-grade re-run (2026-10-13, 02:09–03:05 UTC)

Delta since the previous round. **No prior statement of Theorem C found.**
- **arXiv:** 33 queries on submitted and last-updated dates for 2026-10-12..13, plus 2026-09-20..10-13;
  full-text checks of 12 Euclidean-Ramsey-adjacent PDFs. Only known items. *Caveat:* the arXiv API
  index showed nothing submitted after 2026-10-09 ~18:00Z (announcement lag).
- **arXiv:2609.23327:** v1 only (v2 returns 404). Its Comments field states that the manuscript was
  written entirely by ChatGPT.
- **openai/math:** HEAD `1581d4cb`. The two commits after `fd4aeeb2` only add a PR-lock workflow. Forks
  pushed since 2026-10-12 carry no unique content.
- **GitHub:** repository, README and code searches for repos created or pushed since 2026-10-12 found no
  third-party match. JD-Jones-ASES/six-concyclic-lean, atimics/math2 and Rogerhu12/openai-math-extensions
  have no new Möbius-related commits.
- **Palomar:** 527 entries (revision 252) plus the feed; no Euclidean-Ramsey or Möbius entry beyond
  JD-Jones's v1.
- **MathOverflow and math.stackexchange** (Stack Exchange API, 2026): nothing relevant.
- **OpenAlex, Semantic Scholar, HAL:** nothing relevant.
- **New nearest framing:** Gibbons–Luo, arXiv:1307.5351 (2013), proposes "inversive Ramsey theory"
  (the Möbius group replacing the Euclidean group). It does not state Theorem C. It is cited in the note.
- **Kříž 1991** (Proc. AMS 112, 899–907) was **read in full** (AMS free back issue). It contains no
  Möbius, inversion, conformal, cross-ratio, projective or stereographic content.

## Not read

- Kříž, *All trapezoids are Ramsey* (Discrete Math. 1992): the publisher site serves a challenge
  page; library access is needed. A Möbius remark there is a priori unlikely.
- About 50 of the GitHub follow-up repositories of the OpenAI release were not enumerated
  individually in the second round (the third round's code scan covered 145).
- Lean Zulip, ResearchGate and Google Scholar were not searched (HAL was, in the re-run).

## Still to do (immediately before release)

- Re-run the arXiv queries and the GitHub enumeration; check openai/math HEAD and the Palomar
  registry feed.
- Check arXiv:2609.23327 for a v2. (Done 2026-10-13: v1 only.)
- Read Kříž 1991 (done 2026-10-13) and 1992 (still unread).
- Because of the arXiv index lag, repeat the arXiv queries at the moment of release.

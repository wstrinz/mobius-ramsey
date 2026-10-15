# Citation sources for `note/mobius.tex`

*Record of 2026-10-13, before release; the `\TODO` markers mentioned below were resolved or dropped before v1.0.0.*

How each bibliographic entry and each theorem location in the note was verified. The checks were
made by an AI agent (Claude; see `DISCLOSURE.md`) on 2026-10-13, read-only, from publisher,
Crossref, zbMATH, arXiv, GitHub and Google Books records. Nobody read the books cover to cover.

Marks:
- **READ**: the record or page itself was read, such as an arXiv abstract page or a file at a
  pinned commit.
- **EXTRACT**: a structured metadata record was read (Crossref, zbMATH, the publisher's book
  page). This verifies the bibliographic data, not the content.
- **SNIPPET**: only Google Books "search inside" snippets were seen. This verifies a theorem
  number, page and wording fragment, but not the full statement or its hypotheses.

## The identification Möb(S^{d-1}) ≅ PO(1,d) (§2 of the note)

### Ratcliffe, *Foundations of Hyperbolic Manifolds*, 3rd ed. (2019)

- Bibliographic data: EXTRACT. The Springer book page and Crossref give GTM 149, Springer, Cham,
  2019, doi:10.1007/978-3-030-31597-9, ISBN 978-3-030-31596-2 (hardcover) and 978-3-030-31597-9
  (eBook). zbMATH: Zbl 1430.51002. Chapter 3 is "Hyperbolic Geometry", Chapter 4 is "Inversive
  Geometry" (pp. 97-141) and Chapter 5 is "Isometries of Hyperbolic Space".
- Locations: SNIPPET, from Google Books volume `yMO4DwAAQBAJ` (the 2019 eBook, ISBN
  9783030315979, 800 pp.):
  - p. ix (preface to the 3rd edition): the positive Lorentz group is now written O⁺(n,1), and
    PO(n,1) now means the projective Lorentz group O(n,1)/{±I}. This is the note's PO.
  - p. 61, Theorem 3.2.3: positive Lorentz transformations of R^{n+1} restrict to isometries of
    H^n, and every isometry of H^n extends uniquely to one.
  - p. 62, §3.2 Corollary 3: restriction is an isomorphism from the positive Lorentz group onto
    I(H^n).
  - p. 116: a Möbius transformation of S^n is defined by conjugating with stereographic
    projection.
  - p. 117, §4.4 Corollary 3 (after Theorem 4.4.5): Poincaré extension is an isomorphism from
    M(S^{n-1}) onto M(B^n), and it maps the orientation-preserving subgroups onto each other. So
    M(S^{n-1}) contains the orientation-reversing maps.
  - p. 121, Theorem 4.5.2: Möbius transformations of B^n restrict to isometries of the conformal
    ball model, and every isometry extends to a unique Möbius transformation.
  - p. 122, §4.5 Corollary 1: restriction is an isomorphism from M(B^n) to I(B^n).
  - Also seen, not cited: p. 129, §4.6 Corollary 2, I(H^n) ≅ M(Ê^{n-1}); pp. 152-153, Theorems
    5.2.10-5.2.11, the same isomorphisms as topological groups.
- Ratcliffe's time coordinate is the last one. The note's is the first.
- A secondary check agrees with these numbers: arXiv:1902.05003 cites "Theorem 4.5.2" and
  "Corollary 1 on p. 125" of the 2nd edition (2006) for the same facts. So at least these two
  numbers are the same in both editions, while the pages differ. Cite the 3rd edition.
- Not seen: none of the snippets states the whole composite in one place. That is why the note
  calls it "the composite" of the cited steps.

### Beardon, *The Geometry of Discrete Groups* (1983)

- Bibliographic data: EXTRACT. Crossref gives doi:10.1007/978-1-4612-1146-4, Springer New York,
  1983, GTM, ISBN 9781461270225 and 9781461211464. zbMATH: Zbl 0528.30001 (GTM 91, XII+337 pp.).
- Locations: SNIPPET, from Google Books volume `IpDqBwAAQBAJ` (the eBook, ISBN 9781461211464,
  pagination of the 1983 edition):
  - p. ix: the contents of Chapter 3, "Möbius Transformations on R^n", include §3.7 "The
    Topological Group Structure" (p. 45).
  - p. 49, Theorem 3.7.5: the map F carries the hyperboloid model Q isometrically onto the ball.
  - p. 50, Theorem 3.7.6: the isometries of Q are exactly the matrices that preserve the
    quadratic form and the half-space x₀ > 0.
  - pp. 53-54: O(1,n) is written with the time coordinate first (J = diag(1, -I_n)). Beardon
    concludes that the isometries of Q are exactly O⁺(1,n), and that A ↦ F(A)F⁻¹ is an
    isomorphism of O⁺(1,n) onto GM(B^n), the full Möbius group of the ball. Under this
    isomorphism SO⁺(1,n) corresponds to the orientation-preserving elements. GM(R̂^n), with the
    topology of uniform convergence in the chordal metric, is isomorphic as a topological group
    to O⁺(1,n+1).
- Beardon acts on row vectors (xA). The note acts on column vectors.

### Ahlfors, *Möbius transformations in several dimensions* (1981)

> **Dropped from the note (2026-10-13, coordinator).** His SO(n,1) convention could not be verified beyond search snippets. Ratcliffe and Beardon carry the identification. Kept here as a record.

- Bibliographic data: EXTRACT. zbMATH Zbl 0517.30001 gives Ordway Professorship Lectures in
  Mathematics, University of Minnesota, School of Mathematics, Minneapolis, 1981, 150 pp. There
  is no ISBN or DOI. The note's old entry, "Univ. of Minnesota lecture notes", was corrected to
  the series name.
- Location: SNIPPET, from Google Books volume `Lk_vAAAAMAAJ` (1981; no preview, search snippets
  only):
  - Chapter III, "Hyperbolic geometry", begins on p. 31. Its §3.1 says that one aim of the
    chapter is to represent Möbius groups as matrix groups.
  - p. 37, §3.7, Theorem 1: the groups M(R̂^{n-1}) and SO(n,1) are isomorphic. The quadratic
    form is x₀² − x₁² − … − x_n², with the time coordinate first.
  - p. 40: the proof ends by combining this with §3.5, M(B^n) ≅ M(R̂^{n-1}).
- **Open:** a snippet just before Theorem 1 suggests that Ahlfors fixes what he means by SO(n,1)
  by a definition ("used this property as definition"), presumably by preserving a sheet of the
  hyperboloid. The definition itself was not seen. The note keeps a visible `\TODO` for checking
  it against PO(1,d).

## Journal articles (bibliography)

All are EXTRACT from the publisher's DOI metadata through Crossref. The DOIs, volumes, issues
and page ranges were added to the note.

| key | record |
|---|---|
| EGMRSS | J. Combin. Theory Ser. A 14 (1973), no. 3, 341-363, doi:10.1016/0097-3165(73)90011-3 |
| FR86 | Trans. Amer. Math. Soc. 297 (1986), no. 2, 777-779, doi:10.1090/S0002-9947-1986-0854099-6 |
| Kriz91 | Proc. Amer. Math. Soc. 112 (1991), no. 3, 899-907, doi:10.1090/S0002-9939-1991-1065087-9 |
| Kriz92 | Discrete Math. 108 (1992), no. 1-3, 59-62, doi:10.1016/0012-365X(92)90660-8 |
| LRW12 | J. Combin. Theory Ser. A 119 (2012), no. 2, 382-396, doi:10.1016/j.jcta.2011.09.005 |

The same authors also wrote *Transitive sets and cyclic quadrilaterals*, J. Comb. 2 (2011),
457-462, doi:10.4310/JOC.2011.v2.n3.a6. It was noted here but not checked against the priority
statement. `PRIOR-WORK-SEARCH.md` covers arXiv 1012.1350 and 1012.5468.

## Other entries

- **OAI172:** READ. At openai/math `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, the preprint
  directory named in the entry exists, and its `build/main.tex` has the title "A classification of
  finite Euclidean Ramsey configurations", author OpenAI and date September 23, 2026. The quoted
  passages pass `note/check_verbatim.py` (REPRODUCE.md §6).
- **Palvolgyi:** READ. On the arXiv abstract page for 2609.23327, the title, author and v1 date
  (Sun, 20 Sep 2026) match, and the primary class is math.CO. Only v1 existed on 2026-10-13. The
  posting-day `\TODO` stays.
- **JDJones, Atimics, Rogerhu:** READ (GitHub API, 2026-10-13). None of the three repositories
  has a `CITATION.cff` or written citation instructions, so the "author's preferred citation"
  `\TODO`s stay. Asking the authors is left to the note's author. JD-Jones-ASES/six-concyclic-lean's own
  `formalization.yaml` lists its author as "JD Jones", and its note is titled "Six concyclic
  points satisfy the Euclidean Ramsey tensor criterion". By their commit messages, its two
  commits of 2026-10-12 change only licence and title metadata. Its README and
  `formalization.yaml` contain no Möbius/cross-ratio statement.
- **Comparator:** unchanged; not a bibliographic record.

## BibTeX

These entries are checked against the records above, for use if the note moves to BibTeX. The
note itself uses `thebibliography`.

```bibtex
@book{Ratcliffe,
  author    = {Ratcliffe, John G.},
  title     = {Foundations of Hyperbolic Manifolds},
  edition   = {Third},
  series    = {Graduate Texts in Mathematics},
  volume    = {149},
  publisher = {Springer, Cham},
  year      = {2019},
  doi       = {10.1007/978-3-030-31597-9},
  isbn      = {978-3-030-31596-2},
  note      = {Zbl 1430.51002}
}
@book{Beardon,
  author    = {Beardon, Alan F.},
  title     = {The Geometry of Discrete Groups},
  series    = {Graduate Texts in Mathematics},
  volume    = {91},
  publisher = {Springer-Verlag, New York},
  year      = {1983},
  doi       = {10.1007/978-1-4612-1146-4},
  note      = {Zbl 0528.30001}
}
@book{Ahlfors,
  author    = {Ahlfors, Lars V.},
  title     = {M{\"o}bius Transformations in Several Dimensions},
  series    = {Ordway Professorship Lectures in Mathematics},
  publisher = {University of Minnesota, School of Mathematics},
  address   = {Minneapolis, MN},
  year      = {1981},
  note      = {Zbl 0517.30001}
}
@article{EGMRSS,
  author  = {Erd{\H{o}}s, P. and Graham, R. L. and Montgomery, P. and Rothschild, B. L. and
             Spencer, J. and Straus, E. G.},
  title   = {Euclidean {R}amsey theorems. {I}},
  journal = {J. Combin. Theory Ser. A},
  volume  = {14},
  number  = {3},
  pages   = {341--363},
  year    = {1973},
  doi     = {10.1016/0097-3165(73)90011-3}
}
@article{FR86,
  author  = {Frankl, P. and R{\"o}dl, V.},
  title   = {All triangles are {R}amsey},
  journal = {Trans. Amer. Math. Soc.},
  volume  = {297},
  number  = {2},
  pages   = {777--779},
  year    = {1986},
  doi     = {10.1090/S0002-9947-1986-0854099-6}
}
@article{Kriz91,
  author  = {K{\v{r}}{\'\i}{\v{z}}, Igor},
  title   = {Permutation groups in {E}uclidean {R}amsey theory},
  journal = {Proc. Amer. Math. Soc.},
  volume  = {112},
  number  = {3},
  pages   = {899--907},
  year    = {1991},
  doi     = {10.1090/S0002-9939-1991-1065087-9}
}
@article{Kriz92,
  author  = {K{\v{r}}{\'\i}{\v{z}}, Igor},
  title   = {All trapezoids are {R}amsey},
  journal = {Discrete Math.},
  volume  = {108},
  number  = {1-3},
  pages   = {59--62},
  year    = {1992},
  doi     = {10.1016/0012-365X(92)90660-8}
}
@article{LRW12,
  author  = {Leader, Imre and Russell, Paul A. and Walters, Mark},
  title   = {Transitive sets in {E}uclidean {R}amsey theory},
  journal = {J. Combin. Theory Ser. A},
  volume  = {119},
  number  = {2},
  pages   = {382--396},
  year    = {2012},
  doi     = {10.1016/j.jcta.2011.09.005}
}
@misc{Palvolgyi,
  author        = {P{\'a}lv{\"o}lgyi, D{\"o}m{\"o}t{\"o}r},
  title         = {A cyclic non-{R}amsey heptagon},
  year          = {2026},
  eprint        = {2609.23327},
  archivePrefix = {arXiv},
  primaryClass  = {math.CO},
  note          = {v1, 2026-09-20}
}
```

Given names: the Crossref records give Igor Kříž (both papers), Imre Leader, Paul A. Russell,
Mark Walters, Peter Frankl and Vojtěch Rödl, and only initials for the 1973 authors. The note keeps
initials throughout.

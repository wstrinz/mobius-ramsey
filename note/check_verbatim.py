"""Check that the quoted material in note/mobius.tex is verbatim.

applies_to: note/mobius.tex of this repository only (the two OpenAI #172 quotations and the Lean
excerpt files under note/excerpts/). It checks text identity, not mathematics.

1. OpenAI #172 Theorem 1.1 (with the setup paragraph before it) and Proposition 2.1 (with the
   tensor-condition paragraph before it): the quote blocks in mobius.tex must equal OpenAI's TeX
   source at commit fd4aeeb2, after the documented label/reference edits (EDITS below), up to
   whitespace.
2. The Lean excerpts must equal the stated line ranges of this repository's Lean files, byte for
   byte, and the OpenAI definitions excerpt must equal lines 9-17 of upstream Model.lean (if given)
   and occur verbatim in the ported OAI/Combinatorics/EuclideanRamsey/Model.lean.

Usage (from the repository root):
    python note/check_verbatim.py OAI_SECTIONS_DIR [OAI_MODEL_LEAN]

OAI_SECTIONS_DIR holds 01-introduction.tex and 02-tensors.tex from
preprints/A-classification-of-finite-Euclidean-Ramsey-configurations-September-23-2026/build/
sections/ at openai/math commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. OAI_MODEL_LEAN is
lean/OAI/Combinatorics/EuclideanRamsey/Model.lean at the same commit (optional). See REPRODUCE.md.
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, ".."))

# OpenAI source text -> text as printed in mobius.tex. These are the only edits.
EDITS = [
    (r"\begin{theorem}[Classification]\label{thm:classification}",
     r"\begin{oaithm}[Classification]"),
    (r"\end{theorem}", r"\end{oaithm}"),
    (r"\label{eq:field-evaluations}", r"\tag{1}"),
    (r"\label{eq:field-spatial}", r"\tag{2}"),
    (r"\begin{equation}\label{alg:tensor}", r"\begin{equation}"),
    (r"G(T)=I_d.", r"G(T)=I_d.\tag{3}"),
    (r"\begin{proposition}\label{alg:equivalence}", r"\begin{oaiprop}"),
    (r"\end{proposition}", r"\end{oaiprop}"),
    (r"Theorem~\ref{thm:classification}", r"Theorem~1.1"),
    (r"to~\eqref{alg:tensor}.", r"to~(3)."),
]

LEAN = [
    # (excerpt, source, first line, last line)
    ("excerpts/Defs-L32-43.txt", "MobiusRamsey/Defs.lean", 32, 43),
    ("excerpts/Defs-L48-49.txt", "MobiusRamsey/Defs.lean", 48, 49),
    ("excerpts/Theorem-L68-72.txt", "MobiusRamsey/Theorem.lean", 68, 72),
    ("excerpts/Corollaries-L30-35.txt", "MobiusRamsey/Corollaries.lean", 30, 35),
    ("excerpts/Corollaries-L67-68.txt", "MobiusRamsey/Corollaries.lean", 67, 68),
    ("excerpts/Corollaries-L72-73.txt", "MobiusRamsey/Corollaries.lean", 72, 73),
]


def norm(s):
    return re.sub(r"\s+", " ", s).strip()


def span(text, start, end):
    i = text.index(start)
    j = text.index(end, i) + len(end)
    return text[i:j]


def quotes(tex):
    blocks = re.findall(r"\\begin\{quote\}(.*?)\\end\{quote\}", tex, flags=re.S)
    assert len(blocks) == 2, f"expected 2 quote blocks, found {len(blocks)}"
    return blocks


def edited(s):
    for a, b in EDITS:
        s = s.replace(a, b)
    return s


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return 2
    sec = sys.argv[1]
    ok = True
    tex = open(os.path.join(HERE, "mobius.tex"), encoding="utf-8").read()
    q1, q2 = quotes(tex)
    intro = open(os.path.join(sec, "01-introduction.tex"), encoding="utf-8").read()
    tens = open(os.path.join(sec, "02-tensors.tex"), encoding="utf-8").read()
    src1 = span(intro, "A singleton is Ramsey. For any other set", r"\end{theorem}")
    src2 = span(tens, r"Throughout, $s\geq2$", r"\end{proposition}")
    for name, q, src in (("Theorem 1.1", q1, src1), ("Proposition 2.1", q2, src2)):
        same = norm(q) == norm(edited(src))
        ok &= same
        print(f"{name}: {'VERBATIM' if same else 'DIFFERS'}")
        if not same:
            a, b = norm(q), norm(edited(src))
            k = next((i for i in range(min(len(a), len(b))) if a[i] != b[i]), min(len(a), len(b)))
            print("  note:", a[max(0, k - 60):k + 60])
            print("  oai :", b[max(0, k - 60):k + 60])
    for exc, srcpath, lo, hi in LEAN:
        src = open(os.path.join(ROOT, srcpath), "rb").read().split(b"\n")
        want = b"\n".join(src[lo - 1:hi]) + b"\n"
        got = open(os.path.join(HERE, exc), "rb").read()
        same = got == want
        ok &= same
        print(f"{exc} vs {srcpath}:{lo}-{hi}: {'VERBATIM' if same else 'DIFFERS'}")
    got = open(os.path.join(HERE, "excerpts", "OAI-Model-L9-17.txt"), "rb").read()
    if len(sys.argv) > 2:
        src = open(sys.argv[2], "rb").read().split(b"\n")
        want = b"\n".join(src[8:17]) + b"\n"
        same = got == want
        ok &= same
        print(f"excerpts/OAI-Model-L9-17.txt vs upstream Model.lean:9-17: {'VERBATIM' if same else 'DIFFERS'}")
    else:
        print("excerpts/OAI-Model-L9-17.txt vs upstream Model.lean: SKIPPED (not given)")
    ported = open(os.path.join(ROOT, "OAI", "Combinatorics", "EuclideanRamsey", "Model.lean"), "rb").read()
    same = got in ported
    ok &= same
    print(f"excerpts/OAI-Model-L9-17.txt in OAI/.../Model.lean: {'VERBATIM' if same else 'DIFFERS'}")
    print("ALL VERBATIM" if ok else "MISMATCH")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())

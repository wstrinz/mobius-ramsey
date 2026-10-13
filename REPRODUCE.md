# Reproducing the checks

Everything below runs from the repository root. Network access is needed for the Lean toolchain,
for step 2 (Lake's dependency repositories and the Mathlib cache), and for steps 5 and 6 (files
from openai/math at a pinned commit). Steps 1 to 4 are the Lean result; steps 5 and 6 check
provenance and the note.

## 0. Requirements

- **Linux** with `bash`, `python3` and **bubblewrap** (`bwrap`; e.g. `sudo apt-get install
  bubblewrap`). On Ubuntu 24.04, unprivileged user namespaces may first need
  `sudo sysctl -w kernel.apparmor_restrict_unprivileged_userns=0`. Check that the sandbox starts:
  `bwrap --ro-bind / / --unshare-user --unshare-net true; echo $?` should print `0`.
- **elan** (the Lean toolchain manager), with its `bin` directory on `PATH`. If it is not
  installed, use the official installer (from https://github.com/leanprover/elan):

  ```sh
  curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
  ```

  It installs into `~/.elan`. Non-login shells often miss `~/.elan/bin`, so put it on `PATH`
  explicitly in every shell you use for the steps below:

  ```sh
  export PATH="$HOME/.elan/bin:$PATH"
  ```

  `lean-toolchain` pins `leanprover/lean4:v4.35.0-rc2`; elan installs it on first use. That
  toolchain bundles everything the judge needs: `lake comparator`, `leanexport`, `leanchecker`,
  `nanoda_bin` and `con-ron`.
- **Disk and memory:** about 8 GB of disk (mostly Mathlib's prebuilt files) and about **16 GB of
  RAM**.
- **Time:** about 2 to 4 hours for all steps on a shared machine; see the table at the end.

## 1. Source rules (Palomar)

```sh
python3 scripts/check-lean-sources.py; echo "exit $?"
```

Expected: no output, `exit 0`. Every `.lean` file uses the module system and is under 10,000
lines.

## 2. Mathlib cache and build

`lake exe cache get` needs network access. On a fresh checkout Lake first git-clones, from
GitHub, every dependency pinned in `lake-manifest.json` (mathlib, plausible, LeanSearchClient,
importGraph, proofwidgets, aesop, Qq, batteries, Cli), and may build Mathlib's `cache`
executable; only then does it download and decompress the prebuilt Mathlib files (about 5 GB).
On a cold machine allow roughly 10 to 30 minutes for this command, depending on bandwidth; most
of it is the Mathlib clone and the cache download.

```sh
lake exe cache get
lake build 2>&1 | tee build.log
grep "depends on axioms" build.log
```

Expected: `Build completed successfully`, and every `depends on axioms` line ends with
`[propext, Classical.choice, Quot.sound]`. Among them:

```
'OAI.EuclideanRamsey.Mobius.ramsey_iff_ramsey_mobius_full' depends on axioms: [propext, Classical.choice, Quot.sound]
'OAI.EuclideanRamsey.Mobius.ramsey_mobius_of_algebraic' depends on axioms: [propext, Classical.choice, Quot.sound]
'OAI.EuclideanRamsey.Mobius.ramsey_circ_mul_rat' depends on axioms: [propext, Classical.choice, Quot.sound]
'OAI.EuclideanRamsey.Mobius.ramsey_circ_add_rat' depends on axioms: [propext, Classical.choice, Quot.sound]
'OAI.EuclideanRamsey.ramsey_of_algebraic' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Expected warnings** (not errors):
- four `declaration uses 'sorry'` warnings for `Challenge.lean`. That file is the statement-only
  challenge, and its `sorry`s are the intended holes;
- two `This simp argument is unused` linter warnings in `MobiusRamsey/AlgebraicRamsey.lean`
  (line 120), from a linter newer than the code.

## 3. The judge: Comparator with three kernels, sandboxed

```sh
bash scripts/verify-comparator.sh; echo "exit $?"
```

This is PalomarTemplate's script, unmodified. It writes a temporary copy of `comparator.json`
with the toolchain's NanoDa and con-ron registered as external kernels, as the Palomar registry
does, and runs `lake comparator` in its bubblewrap sandbox. Expected, at the end:

```
Your solution is okay!
exit 0
```

before which con-ron, NanoDa and the Lean kernel each report acceptance of the exported
declarations.

## 4. Negative controls

```sh
bash tests/controls/run-controls.sh; echo "exit $?"
```

Expected: five lines, then `exit 0`:

```
REFUSED as expected: sorry-solution (exit 1): Illegal axiom detected: 'sorryAx'
REFUSED as expected: redef-ramsey (exit 1): Const does not match between challenge and target 'OAI.EuclideanRamsey.Ramsey'
REFUSED as expected: redef-lorentz (exit 1): Const does not match between challenge and target 'OAI.EuclideanRamsey.Mobius.lorentzForm'
REFUSED as expected: redef-circ (exit 1): Const does not match between challenge and target 'OAI.EuclideanRamsey.Mobius.circ'
REFUSED as expected: drop-injective (exit 1): Challenge and solution theorem statement do not match: 'OAI.EuclideanRamsey.Mobius.ramsey_iff_ramsey_mobius_full'
```

`lake comparator` ignores `lake -f`, so the script appends the `Controls` library
(`tests/controls/Controls/`) to `lakefile.toml` while it runs and restores the file on exit.

## 5. Provenance of OpenAI's files

This downloads the 28 upstream files from openai/math at `fd4aeeb2`, re-applies the header-only
port with `scripts/port_to_modules.py`, and compares the result with
`OAI/Combinatorics/EuclideanRamsey/` (also `docs/PORT-LOG.md` §4). Start in the repository root.
The work happens in a fresh scratch directory, because `port_to_modules.py` rewrites the files it
is given in place.

```sh
REPO="$PWD"                      # the repository root
R=fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
SCRATCH="$(mktemp -d)"           # scratch directory for the upstream files
cd "$SCRATCH"
for f in AdicLifting ColoringCompactness Congruence CornerGroup CorrectionPaths DerivedFractions \
         DifferentialSplitting Discretization FiniteEuclidean GramCompletion Hessian LatticeMoments \
         Main Model NormalCost OrbitAveraging PathFractions PathSynchronization PathWords \
         RationalConvolution SignedRows SmoothingKernel SmoothingMatrix StencilConvolution \
         TensorDescent TensorNecessity TensorPresentation UltrafilterStrings; do
  curl -sSfLO "https://raw.githubusercontent.com/openai/math/$R/lean/OAI/Combinatorics/EuclideanRamsey/$f.lean"
done
python3 "$REPO/scripts/port_to_modules.py" --notice-oai "$SCRATCH"/*.lean
diff -r "$SCRATCH" "$REPO/OAI/Combinatorics/EuclideanRamsey" && echo "no differences"
cd "$REPO"
```

Expected: 28 lines `...: ported (1 imports)`, then `no differences`.

## 6. The note's quotations

```sh
R=fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
P=preprints/A-classification-of-finite-Euclidean-Ramsey-configurations-September-23-2026/build/sections
mkdir -p /tmp/oai172
for f in 01-introduction.tex 02-tensors.tex; do
  curl -sSfL -o /tmp/oai172/$f "https://raw.githubusercontent.com/openai/math/$R/$P/$f"
done
curl -sSfL -o /tmp/oai172/Model.lean \
  "https://raw.githubusercontent.com/openai/math/$R/lean/OAI/Combinatorics/EuclideanRamsey/Model.lean"
python3 note/check_verbatim.py /tmp/oai172 /tmp/oai172/Model.lean
```

Expected: every line `VERBATIM`, then `ALL VERBATIM`.

**Optional: building the note.** This is not needed for the Lean result or for any check above.
Run `lualatex mobius.tex` twice in `note/` (it needs a Unicode engine for the Lean excerpts). The
note loads `iftex`, `fontspec`, `geometry`, `amsmath`, `amssymb`, `amsthm`, `mathrsfs`,
`booktabs`, `verbatim`, `xcolor` and `hyperref`, and uses the JuliaMono font if installed, else
DejaVu Sans Mono. On Debian or Ubuntu these should be covered by

```sh
sudo apt-get install texlive-luatex texlive-latex-recommended texlive-latex-extra \
  texlive-fonts-recommended fonts-dejavu-core
```

(`fontspec` comes with `texlive-luatex`, `mathrsfs` with `texlive-latex-extra` and
`texlive-fonts-recommended`; `texlive-full` covers everything). The note has not yet been built
with this package list.

## Windows without a sandbox

`bwrap` does not exist on Windows. The same check runs unsandboxed, which `lake comparator` reports
as "not trustworthy" (the sandbox protects the judge from hostile code; it does not change the
verdict). On Windows the kernel executables need the `.exe` suffix: copy `comparator.json`, drop
`enable_nanoda`, add

```json
"external_kernels": {"nanoda": ["<prefix>/bin/nanoda_bin.exe"], "con-ron": ["<prefix>/bin/con-ron.exe"]}
```

with `<prefix>` from `lean --print-prefix`, and run
`lake comparator --config <that file> --inadvisably-no-sandbox`. The controls run the same way
with `bash tests/controls/run-controls.sh --no-sandbox` (Git Bash).

## Measured times

Measured on one shared desktop machine (other work running), with Mathlib's files already in the
local cache. A cold download of the Mathlib cache (about 5 GB) adds its own time.

| Step | Linux (WSL Ubuntu, 8 threads, 15 GB) | Windows (12 threads) |
|---|---|---|
| `lake exe cache get` | 3.5 min | (not timed) |
| `lake build`, first time (OpenAI's 28 modules build one after another) | 8.5 min | 32 min |
| `lake build` after a change to `MobiusRamsey/Defs.lean` | (not timed) | 5.7 min |
| `scripts/verify-comparator.sh` (export, three kernels; about 63,600 declarations) | 8.3 min | (sandbox unavailable) |
| `tests/controls/run-controls.sh` (five controls) | 11.8 min | 33.5 min (`--no-sandbox`) |

On a heavily loaded machine an earlier, similar package took about 2.5 hours to build and 13 to
32 minutes per Comparator run, so allow **2 to 4 hours** in the worst case. Peak memory stayed
within 16 GB.

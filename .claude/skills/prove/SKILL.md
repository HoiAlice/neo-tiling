---
name: prove
description: Prove a mathematical statement in Lean 4 + Mathlib inside this repo. Use when asked to prove, formalize, or fix a Lean theorem, or to close a sorry.
argument-hint: "[statement in words or in Lean]"
allowed-tools: "Read, Edit, Write, Grep, Glob, Bash(lake env lean:*), Bash(lake build:*)"
---

Prove the following in Lean 4 with Mathlib:

$ARGUMENTS

## Project facts

- Toolchain `v4.28.0-rc1`, Mathlib is prebuilt. `import Mathlib` works.
- Source files live in `NeoTiling/`. Existing files: !`ls NeoTiling/`
- Check a file with `lake env lean NeoTiling/<File>.lean`, run from the repo root.
  One run takes 4 to 9 seconds, most of it loading Mathlib. Read the whole output.
- Never touch `lean-toolchain`, `lakefile.lean`, `lake-manifest.json`. Never run `lake update`.

## Workflow

1. **State first, prove second.** If the request names an existing file and theorem
   (typically the output of `/formulate`), prove it in place and do not change its
   statement. Otherwise pick a file in `NeoTiling/` by topic (create one if
   needed, starting with `import Mathlib`). Write the `theorem` with a `sorry` body and
   run the checker. If the statement itself does not typecheck, fix the statement.
   If the request was informal, show the user the Lean statement you chose before
   spending effort on the proof, and say what you assumed (domain ℕ vs ℝ, strictness,
   edge cases like `n = 0`).

2. **Search Mathlib before proving.** In order: `exact?`, then `apply?`, then `rw?`,
   then `grep -rn` under `.lake/packages/mathlib/Mathlib` for keywords and
   Mathlib-style names (`add_comm`, `Finset.sum_range_succ`, `Real.sqrt_le_sqrt`).
   `exact?` failing is common; it does not mean the lemma is absent.

3. **Tactic by goal shape.**
   - linear arithmetic over ℕ/ℤ: `omega`
   - linear over ordered fields: `linarith`; nonlinear: `nlinarith [sq_nonneg (a - b), ...]`
     with hints; `positivity` for `0 ≤ _` / `0 < _`
   - numerals: `norm_num`; decidable finite facts: `decide`
   - ring identities: `ring`; with division: `field_simp` then `ring`
   - monotonicity of compound expressions: `gcongr`
   - logic, sets, structural routine: `simp`, `aesop`, `tauto`
   - sums and products over `Finset.range`: `induction n with | zero => simp | succ k ih => rw [Finset.sum_range_succ, ih]; ring`

4. **One step, then recheck.** After each edit run the checker. The `unsolved goals`
   block shows the exact goal state; use it instead of guessing. Do not stack several
   blind edits between runs.

5. **Split when long.** Above roughly 15 lines, extract lemmas. Leaving `sorry` in a
   helper lemma is allowed only if the final report lists it.

6. **Done** when the checker prints nothing or only warnings, the file has no `sorry`
   (or every remaining `sorry` is listed), and `lake build` succeeds.

## Do not

- weaken the statement without saying so;
- use `native_decide` or add axioms;
- keep grinding a goal that has not moved in 5 attempts. Stop, report the goal state
  and what was tried, and ask the user for a mathematical hint.

## Report

File and theorem name, final statement, list of remaining `sorry`, Mathlib lemmas
used, and anything that did not work and why.

---
name: formulate
description: Translate an informal mathematical statement into a precise Lean 4 + Mathlib theorem statement, check that it typechecks and that it faithfully says what was asked, and show it. Does not prove anything and does not create files unless asked.
argument-hint: "[statement in words, optionally with definitions and conventions]"
allowed-tools: "Read, Edit, Write, Grep, Glob, Bash(lake env lean:*)"
---

Formalize the following as a Lean 4 theorem statement and show it to the user with an
assessment of how faithfully it captures the informal claim. Do not prove it.

$ARGUMENTS

## Project facts

- Toolchain `v4.28.0-rc1`, Mathlib is prebuilt. `import Mathlib` works.
- Check a snippet without touching the repo, from the repo root:
  ```
  printf '%s\n' 'import Mathlib' '' '<statement> := by sorry' | lake env lean --stdin
  ```
  One run takes 4 to 9 seconds. Expected output for a good statement is only the
  `declaration uses 'sorry'` warning.
- Only write into `NeoTiling/` if the user asks to save the statement. Then: pick or
  create a file by topic (a new file starts with `import Mathlib`), add the theorem
  with a docstring quoting the informal statement and a `sorry` body, and recheck
  the whole file with `lake env lean NeoTiling/<File>.lean`. Existing files: !`ls NeoTiling/`
- Never touch `lean-toolchain`, `lakefile.lean`, `lake-manifest.json`. Never run `lake update`.

## Workflow

1. **Pin down the informal meaning.** Before writing Lean, note for yourself: the
   objects and their domains (ℕ, ℤ, ℚ, ℝ, ℂ, a general type with a class),
   quantifier structure, strict vs non-strict inequalities, edge cases (`n = 0`,
   empty set, division by zero). If the text leaves a choice that changes the theorem,
   either ask the user or, when one reading is clearly intended, pick it and flag it.

2. **Use Mathlib's vocabulary.** `grep -rn` under `.lake/packages/mathlib/Mathlib` for
   the concept (`Nat.Prime`, `Finset.sum`, `IsCompact`, `MeasureTheory.Measure`,
   `Tendsto`). Prefer Mathlib's definitions over ad hoc ones. If a new `def` is
   unavoidable, keep it minimal and show it alongside the theorem.

3. **Write the statement** with a Mathlib-style name and a `sorry` body.

4. **Typecheck via stdin.** Fix errors in the statement until only the `sorry`
   warning remains. Use `#check` on subterms when coercions or numeral types are
   unclear; Lean inserts `↑` coercions silently and they change meaning.

5. **Hunt for mis-formalization.** Replace `sorry` with `plausible` and rerun.
   `Found a counter-example!` with concrete values means the statement is false as
   written; that is almost always a translation error (see pitfalls), not a false
   theorem. `Unable to find a counter-example` is weak evidence the statement is at
   least not obviously wrong. `plausible` only works over sampleable decidable types
   (ℕ, ℤ, ℚ, `Fin n`, `Bool`, lists and finsets of these); for ℝ or abstract
   structures skip it and say so.

6. **Back-translate independently.** Read the final Lean statement as if you had
   never seen the informal text and write out in plain words exactly what it says,
   including what happens at edge cases. Compare with the original request sentence
   by sentence. Every difference is either a deliberate choice to report or a bug to
   fix. Also check for trivialities: an unsatisfiable hypothesis makes any conclusion
   provable, a conclusion implied by the hypotheses alone makes the theorem empty.

## Pitfalls that produce wrong statements

- `ℕ` subtraction truncates: `a - b = 0` when `b ≥ a`. Add `b ≤ a` or move to `ℤ`.
- `ℕ` and `ℤ` division rounds; `x / 0 = 0` in every field. Add `≠ 0` hypotheses or
  state the multiplied-out form.
- `Finset.range n` is `{0, …, n-1}`. Sums "from 1 to n" are over `Finset.Icc 1 n`.
- Numerals default to `ℕ`: `2 * x` with `x : ℝ` is fine, `(1/2) * x` is not,
  write `(1/2 : ℝ) * x`.
- `Real.sqrt`, `Real.log`, `Real.exp` are total: `Real.sqrt` of a negative is `0`,
  `Real.log 0 = 0`.
- `∃!` vs `∃`; `Set.Icc a b` closed interval, `Set.Ioo a b` open.
- "For all sufficiently large n" is `∀ᶠ n in Filter.atTop, …` or the more elementary
  `∃ N, ∀ n ≥ N, …`.
- Limits: `Filter.Tendsto f Filter.atTop (nhds L)`, not an ε-δ unfolding, unless the
  user wants the elementary form.

## What to show

1. The Lean statement verbatim in a code block, with any helper `def`.
2. The back-translation in words, and the list of choices made (domains, strictness,
   edge cases, Mathlib definitions relied on).
3. Result of the typecheck and of the `plausible` check.
4. Any discrepancy with the informal request that you could not resolve, phrased as
   a question to the user.

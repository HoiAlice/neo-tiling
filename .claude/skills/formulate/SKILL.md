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

2. **Use Mathlib's vocabulary.** Ask a `mathlib-search` agent for the concepts involved
   (`Nat.Prime`, `Finset.sum`, `IsCompact`, `MeasureTheory.Measure`, `Tendsto`) and for
   existing `NeoTiling/` definitions, instead of grepping Mathlib in this context. Several
   independent lookups can run in parallel. If the agent type is not found, spawn
   `general-purpose` with model `haiku` and tell it to follow `.claude/agents/mathlib-search.md`.
   Prefer existing definitions over ad hoc ones. If
   a new `def` is unavoidable, keep it minimal and show it alongside the theorem.

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

6. **Back-translate independently.** Spawn a `lean-advisor` agent (Fable) in reader mode
   with `run_in_background: false`. Give it only the final Lean statement with any helper
   `def`, the import it typechecks under, and the files where the definitions it uses live.
   Do not give it the informal text, the request, or any hint of the intended meaning: its
   value is that it cannot read the intent into the statement. If the agent type is not
   found, spawn `general-purpose` with model `fable` and tell it to follow
   `.claude/agents/lean-advisor.md` in reader mode.
   Compare its reading with the original request and the discussion sentence by sentence.
   Every difference is either a deliberate choice to report or a bug to fix. After a fix
   that changes meaning, run the reader again on the new statement.

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
2. The reader's back-translation (condensed), the differences you found and how you
   resolved them, and the list of choices made (domains, strictness, edge cases,
   definitions relied on).
3. Result of the typecheck and of the `plausible` check.
4. Any discrepancy with the informal request that you could not resolve, phrased as
   a question to the user.

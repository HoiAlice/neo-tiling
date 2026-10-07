# neo-tiling

Math notes (`latex/notes.tex`, Russian) and their Lean 4 + Mathlib formalization (`NeoTiling/`).

## Lean proofs

- `/prove` runs in a fresh forked context on Opus (Sonnet workers, Fable `lean-advisor` only when
  stuck) and does not see this conversation. When you invoke it, pass a self-contained brief: file
  and theorem (or statement), the proof idea step by step, conventions agreed in discussion, and
  the relevant section of `latex/notes.tex`. The better the proof idea in the brief, the less
  Fable is needed.
- `/formulate` runs here, on the session model; its independent back-translation goes to
  `lean-advisor` (Fable) with the Lean statement only.
- When `/prove` reports `NEED_HINT`, answer yourself only if the answer follows from what was
  already discussed or from the notes, and tell the user what you answered. Otherwise ask the
  user. Send the answer to that agent with `SendMessage`; it resumes with its context intact.
- If the user asks to prove "here" (without the fork), follow `.claude/skills/prove/SKILL.md` in
  this context, still delegating tactic work to `lean-prover` agents.

## Legacy

`OLD/` holds the pre-2026-10-07 notes (tex, pdf) and Lean library (general position, profiles,
level curves). It is legacy: do not read, reuse or cite it unless the user asks. The lakefile does
not build it.

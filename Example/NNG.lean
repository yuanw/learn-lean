/-
  NNG4, Tutorial world, level 1:
  https://adam.math.hhu.de/#/g/leanprover-community/nng4/world/Tutorial/level/1

  The game's `rfl` is deliberately weaker than core Lean's -- it only closes a goal when
  both sides are *identical as terms* -- so don't reach for `simp`/`omega`/`decide`.
  Same for `rw`: core's `rw` tries `rfl` afterwards, so use `rewrite` to keep the game's
  two-step proofs honest.

  Note: this file uses `Nat`, not the pretty `ℕ`, because `ℕ` notation is not in core
  Lean 4.35 here (it would silently become an auto-bound implicit). Write `import Mathlib`
  at the top if you want `ℕ`.
-/

/-- If `x` and `q` are arbitrary natural numbers, then `37 * x + q = 37 * x + q.` -/
theorem nng_tutorial_1 (x q : Nat) : 37 * x + q = 37 * x + q := by
  rfl
#print axioms nng_tutorial_1

/-- If `x` and `y` are natural numbers, and `y = x + 7`, then `2 * y = 2 * (x + 7).` -/ -- nng4 Tutorial/2
theorem nng_tutorial_2 (x y : Nat) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  rewrite [h]
  rfl
#print axioms nng_tutorial_2

/--
For all natural numbers `a` and `b`, we have `succ a * b = a * b + b.`

nng4 Multiplication/3 (the game calls it `succ_mul`):
https://adam.math.hhu.de/#/g/leanprover-community/nng4/world/Multiplication/level/3

In the game `mul_zero`, `mul_succ`, `add_succ`, `add_right_comm` are lemmas you proved in
Addition/Multiplication world; here the same facts come from core `Nat`, so the proof below
is the game's proof verbatim.
-/
theorem nng_multiplication_3 (a b : Nat) : Nat.succ a * b = a * b + b := by
  induction b with
  | zero =>
    rewrite [Nat.mul_zero, Nat.mul_zero, Nat.add_zero]
    rfl
  | succ d hd =>
    rewrite [Nat.mul_succ, Nat.mul_succ]
    rewrite [hd]
    rewrite [Nat.add_succ, Nat.add_succ, Nat.add_right_comm]
    rfl
#print axioms nng_multiplication_3

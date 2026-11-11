/-!
The predicate as a string, substituted by `String.replace` — book/ Ch 2's opening bug.
Run it: `lean book/code/ch02/predicate-as-string.lean`. Three wrong answers, all of them silent.
-/

/-- A predicate is the text the user wrote inside `/*@ ... */`. -/
def PredS := String

/-- `p[x := t]` by find and replace. -/
def substS (p x t : String) : PredS := p.replace x t

/-- The refinement of `get`'s index argument, from the paper's §1. -/
def idx : PredS := "0 <= x && x < len(xs)"

#eval substS idx "x" "n"
#eval substS idx "x" "n + 1"
#eval substS "0 <= v && v < len(vlen)" "v" "i"

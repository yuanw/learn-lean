/-!
Asking Lean for decidable equality on the AST — book/ Ch 2. THIS FILE IS MEANT TO FAIL.
Run it: `lean book/code/ch02/derive.lean`. `Term`'s `List` field makes the `DecidableEq`
handler refuse; `Pred` then half-derives an instance whose `decide` is `sorry`, which the
`#print axioms` at the end reports.
-/

namespace Sprite

inductive Term where
  | var (x : String)
  | int (n : Int)
  | app (f : String) (args : List Term)
  deriving BEq, Repr, DecidableEq

inductive Pred where
  | tru
  | rel (l r : Term)
  | and (p q : Pred)
  deriving BEq, Repr, DecidableEq

end Sprite

#print axioms Sprite.instDecidableEqPred

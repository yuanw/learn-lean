/-!
Substitution written with `map`, and what the kernel makes of it — book/ Ch 2.
Run it: `lean book/code/ch02/map-version.lean`. The `#eval` is fine; the `#reduce` is 82 lines
of `Acc.rec` that never reach a constructor, which is why `Sprite/Refine.lean` writes the list
recursion out by hand.
-/

namespace Sprite
inductive Term where
  | var (x : String)
  | int (n : Int)
  | arith (l r : Term)
  | app (f : String) (args : List Term)

def Term.substMap : Term → String → Term → Term
  | .var y       => fun x s => if x == y then s else .var y
  | .int _       => fun _ s => s
  | .arith l r   => fun x s => .arith (l.substMap x s) (r.substMap x s)
  | .app f args  => fun x s => .app f (args.map (fun a => a.substMap x s))

end Sprite
open Sprite
#eval (Term.app "len" [Term.var "x"]).substMap "x" (Term.int 1)
#reduce (Term.app "len" [Term.var "x"]).substMap "x" (Term.int 1)

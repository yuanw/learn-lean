/-!
Fig. 2.1 transcribed literally: one grammar for terms and predicates — book/ Ch 2.
Run it: `lean book/code/ch02/one-grammar.lean`. The second and third lines are formulas the
grammar should have refused to build; `junk.smt2` is what z3 makes of the second.
-/

inductive Expr where
  | var  (x : String)
  | int  (n : Int)
  | bool (b : Bool)
  | bin  (l : Expr) (op : String) (r : Expr)
  | and  (l r : Expr)
  | or   (l r : Expr)
  | not  (l : Expr)
  | ite  (c t e : Expr)
  | app  (f : String) (args : List Expr)

def Expr.pp : Expr → String
  | .var x        => x
  | .int n        => toString n
  | .bool b       => toString b
  | .bin l op r   => "(" ++ l.pp ++ " " ++ op ++ " " ++ r.pp ++ ")"
  | .and l r      => "(" ++ l.pp ++ " && " ++ r.pp ++ ")"
  | .or l r       => "(" ++ l.pp ++ " || " ++ r.pp ++ ")"
  | .not l        => "~(" ++ l.pp ++ ")"
  | .ite c t e    => "if " ++ c.pp ++ " then " ++ t.pp ++ " else " ++ e.pp
  | .app f args   => f ++ "(" ++ String.intercalate ", " (args.map Expr.pp) ++ ")"

/-- A well-formed refinement. -/
def ok : Expr := .and (.bin (.int 0) "<=" (.var "v")) (.bin (.var "v") "<" (.app "len" [.var "xs"]))
#eval ok.pp

/-- A formula of type `int`: the conjunction of a comparison and the number 3. Nothing in
    the grammar above stops us writing it, and nothing in the printer notices. -/
def junk : Expr := .and (.bin (.int 0) "<=" (.var "v")) (.int 3)
#eval junk.pp

/-- And the shape Ch 6's parser would hand us if `if` ever lost a branch. -/
def junk2 : Expr := .ite (.bin (.int 0) "<" (.var "x")) (.int 3) (.bool true)
#eval junk2.pp

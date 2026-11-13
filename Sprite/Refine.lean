/-!
# Predicates (Ch 2)

The object language's logic: the quantifier-free predicates of Fig. 2.1 of Jhala & Vazou,
*Refinement Types*, held as Lean data.

Two decisions in this file are load-bearing for the rest of the book.

**Terms and predicates are separate types.** The figure spells one grammar, in which
`0 <= v` and `v + 1` and even `if b then 3 else x` are all "predicates". That is the
faithful transcription of §2.1 — and it lets us build `(0 <= v) && 3`. We split the figure
into `Term` (integer- or boolean-valued) and `Pred` (true or false), which rules out the
category errors and leaves only the leaf-level sort errors — a boolean variable inside an
addition — for the kind checker of Ch 7.

**Nothing here carries a type.** `var "x"` says `x` and nothing else; `app "len" [x]` says
`len` is applied to one argument. The sorts live in the environment the checker carries
(Ch 9) and in the signature table the emitter needs (Ch 3). Keeping them out of the AST is
what lets `subst` below be a total function on syntax with no side conditions — and what
lets its tests be checked by the kernel rather than run.
-/

namespace Sprite

/-- The arithmetic half of Fig. 2.1's interpreted operators `p ⋈ p`.

    `shortcut`: no division, modulo, set or string operators, because none of the 113 corpus
    files uses one. Add a constructor when a file needs it; the compiler will list every
    match site that has to grow. -/
inductive Arith where
  /-- `+` -/
  | add
  /-- `-` -/
  | sub
  /-- `*` -/
  | mul
  deriving Repr

/-- How an `Arith` is written in `.re` source. -/
def Arith.symbol : Arith → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"

/-- The comparisons of Fig. 2.1's `p ⋈ p`, the ones that return a boolean.

    `gt` and `ge` are `lt` and `le` with the arguments swapped, so they are derivable. They
    stay because the printer must print what the source said, and because Ch 3 emits them as
    SMT-LIB `>` and `>=` rather than as an extra `Not` node. -/
inductive Rel where
  /-- `==` -/
  | eq
  /-- `<` -/
  | lt
  /-- `<=` -/
  | le
  /-- `>` -/
  | gt
  /-- `>=` -/
  | ge
  deriving Repr

/-- How a `Rel` is written in `.re` source. -/
def Rel.symbol : Rel → String
  | .eq => "=="
  | .lt => "<"
  | .le => "<="
  | .gt => ">"
  | .ge => ">="

/-- Integer- and boolean-valued expressions: what a `Rel` compares, and what a refinement
    can compute with.

    `bool` and `app` are why this is one type rather than two: `true` and `len(xs)` are terms,
    one of each sort, and a term of boolean sort can stand as a formula through `Pred.holds`
    — the corpus writes the refinement `bool[b|b]` for "this boolean is true"
    (`test/L3/neg/abs01.re`). -/
inductive Term where
  /-- A variable, `x`. Unsorted: the checker's environment says what `x` is. -/
  | var (x : String)
  /-- An integer literal: `0`, `-1`, `42`. -/
  | int (n : Int)
  /-- A boolean literal, `true` or `false`, standing as a *term*. -/
  | bool (b : Bool)
  /-- An interpreted operator application, e.g. `x + 1`. -/
  | arith (o : Arith) (l r : Term)
  /-- An uninterpreted function application, e.g. `len(xs)`. The solver knows nothing of `f`
      beyond the congruence axiom Ch 17 puts into the query. -/
  | app (f : String) (args : List Term)
  deriving Repr

/-- The predicates of Fig. 2.1, quantifier-free.

    A refinement `int[v | p]` is a `Pred` with one distinguished free variable — the *value
    variable* `v`. Ch 4 wraps that pair into a reft; Ch 21 gives this type its meaning. -/
inductive Pred where
  /-- `true`. Spelled `tru` because `true` in a pattern is `Bool.true`. -/
  | tru : Pred
  /-- `false`. -/
  | fls : Pred
  /-- `l op r`, e.g. `0 <= v`. -/
  | rel (op : Rel) (l r : Term) : Pred
  /-- A boolean-valued `Term` standing as a formula: the `b` in `bool[b|b]`, or, from Ch 16,
      an `is-cons(xs)` test. The figure needs no such case because it has no `Term`; this is
      the price of the split. -/
  | holds (t : Term) : Pred
  /-- `p && q` -/
  | and (p q : Pred) : Pred
  /-- `p || q` -/
  | or (p q : Pred) : Pred
  /-- `~p` -/
  | not (p : Pred) : Pred
  /-- `if c then p else q`. The figure keeps it although `(c ⇒ p) ∧ (¬c ⇒ q)` says the same
      thing: Ch 11's path-sensitive typing produces ite-refinements directly, and unwinding
      the abbreviation into implications makes both the query and the error message bigger. -/
  | ite (c p q : Pred) : Pred
  deriving Repr

/-! ## Printing

Every `#eval` in this book, every type error the checker reports, and every file in
`test/golden/` shows a predicate through these functions, so they are part of the checker's
user interface. They are deliberately dumb: a compound subexpression is always
parenthesized, so `and (0 <= v) (v < len xs)` prints as `(0 <= v) && (v < len(xs))`.

That costs some noise and buys two things: no precedence table to keep in sync with the
parser of Ch 6, and `parse (pp p) = p` by construction instead of by argument. Each pair of
parentheses marks exactly where an ambiguity would live. -/

mutual
/-- Source text for a term, e.g. `len(xs) + 1`.

    A negative literal keeps its parentheses: `0 + (-1)` re-parses, whereas `0 + -1` is not a
    term. The `List` case is a mutual definition rather than `args.map Term.pp` because a
    `map` over a recursive function compiles to well-founded recursion, whose `Acc.rec` the
    kernel will not reduce — and we want the tests below checked, not run. -/
  def Term.pp : Term → String
    | .var x       => x
    | .int n       => if 0 ≤ n then toString n else "(" ++ toString n ++ ")"
    | .bool b      => toString b
    | .arith o l r => "(" ++ l.pp ++ " " ++ o.symbol ++ " " ++ r.pp ++ ")"
    | .app f args  => f ++ "(" ++ Term.ppList args ++ ")"

  /-- The comma-separated arguments of an application: the `x, 1` in `f(x, 1)`. -/
  def Term.ppList : List Term → String
    | []      => ""
    | [t]     => t.pp
    | t :: as => t.pp ++ ", " ++ Term.ppList as
end

/-- Source text for a predicate, e.g. `(0 <= v) && (v < len(xs))` — the surface syntax of
    Ch 5, so that a printed predicate is legal sprite. -/
def Pred.pp : Pred → String
  | .tru       => "true"
  | .fls       => "false"
  | .rel o l r => "(" ++ l.pp ++ " " ++ o.symbol ++ " " ++ r.pp ++ ")"
  | .holds t   => t.pp
  | .and p q   => "(" ++ p.pp ++ " && " ++ q.pp ++ ")"
  | .or p q    => "(" ++ p.pp ++ " || " ++ q.pp ++ ")"
  | .not p     => "~(" ++ p.pp ++ ")"
  | .ite c p q => "if " ++ c.pp ++ " then " ++ p.pp ++ " else " ++ q.pp

/-! ## Substitution

`p[x := t]` is the one operation every later chapter asks for: Ch 12 instantiates a `∀x` with
a term, Ch 13 qualifies the results, Ch 21 needs it to say what validity means, and Ch 4 uses
it to read a refinement off a function's type at every application.

It has no side conditions *today* because `Pred` has no binders: `ite` binds nothing, so no
free variable of `t` can be captured and there is nothing to freshen. That is a property of
this AST, not of substitution; when Ch 12 adds `Pred.forall x p`, this function has to rename
and the tests below stop being `rfl`. -/

mutual
/-- `t[x := s]`, replacing every free occurrence of the variable `x` with the term `s`. -/
  def Term.subst (t : Term) (x : String) (s : Term) : Term :=
    match t with
    | .var y       => if x == y then s else .var y
    | .int _       => t
    | .bool _      => t
    | .arith o l r => .arith o (l.subst x s) (r.subst x s)
    | .app f args  => .app f (Term.substList args x s)

  /-- `ts[x := s]`, mapping `subst` over the arguments of an application. Mutual with
      `Term.subst` for the same structural-recursion reason as `Term.ppList`. -/
  def Term.substList (ts : List Term) (x : String) (s : Term) : List Term :=
    match ts with
    | []      => []
    | t :: as => t.subst x s :: Term.substList as x s
end

/-- `p[x := s]`. Terms inside a predicate go through `Term.subst`; the connectives just
    recurse. Note what is *not* here: no freshness check, because nothing binds. -/
def Pred.subst (p : Pred) (x : String) (s : Term) : Pred :=
  match p with
  | .tru       => .tru
  | .fls       => .fls
  | .rel o l r => .rel o (l.subst x s) (r.subst x s)
  | .holds t   => .holds (t.subst x s)
  | .and p q   => .and (p.subst x s) (q.subst x s)
  | .or p q    => .or (p.subst x s) (q.subst x s)
  | .not p     => .not (p.subst x s)
  | .ite c p q => .ite (c.subst x s) (p.subst x s) (q.subst x s)

/-! ## The formulas this chapter is about

Named so that the tests, the prose, and Ch 3's two SMT queries all talk about the same three
predicates. -/

/-- `0 <= v`, the refinement of `nat` (equation 3.1 of the paper). -/
def nonneg (v : String) : Pred :=
  .rel .le (.int 0) (.var v)

/-- `0 < v`, the refinement of `pos`. -/
def positive (v : String) : Pred :=
  .rel .lt (.int 0) (.var v)

/-- `0 <= i && i < len(xs)`: a valid index into the list `xs`. This is the formula that
    decides Ch 2 — it has to be data, not a string. -/
def index (i xs : String) : Pred :=
  .and (nonneg i) (.rel .lt (.var i) (.app "len" [.var xs]))

/-! ## Tests

Each one is `rfl`, so the kernel evaluates `pp` and `subst` and compares the constructor
trees itself; nothing here is run and trusted. That is only possible because every recursion
above is structural — see `Term.ppList`. -/

-- The three formulas the chapter opens with, as the reader will see them in Ch 3.
#eval (index "i" "xs").pp
#eval (nonneg "v").pp
#eval (positive "v").pp

-- Printing distinguishes the formulas a string-based checker would merge.
example : (index "i" "xs").pp = "((0 <= i) && (i < len(xs)))" := rfl
example : (Pred.and (nonneg "i") (Pred.holds (.var "b"))).pp = "((0 <= i) && b)" := rfl
example : (Pred.not (index "i" "xs")).pp = "~(((0 <= i) && (i < len(xs))))" := rfl
example : (Pred.holds (.app "is-nil" [.var "xs"])).pp = "is-nil(xs)" := rfl
example : (Pred.ite (positive "n") (.holds (.var "b")) Pred.fls).pp
          = "if (0 < n) then b else false" := rfl

-- A negative literal prints as `(-1)`, so `(0 + (-1))` cannot re-parse as `0 - 1`.
example : (Term.arith .add (.int 0) (.int (-1))).pp = "(0 + (-1))" := rfl

-- Substitution into the index formula: the index `i` becomes an expression, and the `xs`
-- under `len` is untouched, because `len` is a function symbol and not a variable.
example : (index "i" "xs").subst "i" (.app "len" [.var "ys"])
          = Pred.and (.rel .le (.int 0) (.app "len" [.var "ys"]))
              (.rel .lt (.app "len" [.var "ys"]) (.app "len" [.var "xs"])) := rfl

-- A variable that does not occur is a no-op, on both halves of the AST.
example : (index "i" "xs").subst "j" (.int 0) = index "i" "xs" := rfl
example : (Pred.holds (.app "f" [.var "x", .var "y"])).subst "y" (.int 2)
          = Pred.holds (.app "f" [.var "x", .int 2]) := rfl

-- Substitution reaches under every connective, including the condition of an `ite`.
example : (Pred.not (nonneg "v")).subst "v" (.int 0) = Pred.not (.rel .le (.int 0) (.int 0)) := rfl
example : (Pred.or Pred.tru (.holds (.var "b"))).subst "b" (.var "c")
          = Pred.or Pred.tru (.holds (.var "c")) := rfl
example : (Pred.ite (nonneg "v") (.holds (.var "v")) Pred.fls).subst "v" (.int 1)
          = Pred.ite (.rel .le (.int 0) (.int 1)) (.holds (.int 1)) Pred.fls := rfl

-- Duplicated variables duplicate the substitute: substitution is textual, and Ch 22 will
-- have to say exactly when that is safe.
example : (Term.arith .mul (.var "x") (.var "x")).subst "x" (Term.arith .add (.var "y") (.var "y"))
          = Term.arith .mul (Term.arith .add (.var "y") (.var "y")) (Term.arith .add (.var "y") (.var "y")) := rfl

end Sprite

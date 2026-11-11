# 2. Predicates

*[impl] — 4 h — gate: `lake build` green, thirteen `example`s checked, three `#eval`s printed*

> We will write `p[x := q]` (resp. `c[x := q]`) to denote the (capture avoiding) substitution
> of all (free) occurrences of `x` in `p` (resp. `c`) with `q`.
>
> — Ranjit Jhala and Niki Vazou, *Refinement Types* §2.2

## The bug is in the string

The paper's §1 motivates refinements with a pair of signatures, `size` and `get` over arrays.
The corpus has no arrays; it has `list('a)` with a measure `len`, declared in
[test/L5/pos/append00.re](../test/L5/pos/append00.re). Same example, ours:

```re
/*@ val size : x:list('a) => nat[v|v = len(x)] */
/*@ val get  : x:list('a) => nat[i|0 <= i && i < len(x)] => 'a */
```

The second one is the shape this whole chapter is about. `0 <= i && i < len(x)` says which
subset of `int` the second argument may come from, and the checker — not the programmer — has
to decide, for every call site, that the call's assumptions imply it.

The cheapest thing that could possibly work is to keep the annotation as the text the user
wrote, and paste that text into the SMT-LIB query. Before the solver sees it, two things have
to happen to the text: the value variable has to be replaced by the expression the checker is
looking at (`i := n - 1`, say, at a call `get(xs, n - 1)`), and the formula has to be negated
and conjoined with the path assumptions (Ch 3). Here is the first of those, written the obvious
way:

```lean
/-- A predicate is the text the user wrote inside `/*@ ... */`. -/
def PredS := String

/-- `p[x := t]` by find and replace. -/
def substS (p x t : String) : PredS := p.replace x t

/-- The refinement of `get`'s index argument. -/
def idx : PredS := "0 <= x && x < len(xs)"

#eval substS idx "x" "n"
#eval substS idx "x" "n + 1"
```

```
$ lean book/code/ch02/predicate-as-string.lean
"0 <= n && n < len(ns)"
"0 <= n + 1 && n + 1 < len(n + 1s)"
"0 <= i && i < len(ilen)"
```

Three corruptions. `len(xs)` became `len(ns)` because the `x` inside the *variable name* `xs`
matched — the third line is the same trick on `v` and `vlen`. `n + 1s` is what happens when the
replacer has no idea where one subexpression ends and another begins. None of these is a corner
case: `xs` occurs 240 times in the corpus — it is what the list files call their list — and
every term the checker ever substitutes is bigger than a variable.

Both are the same bug: **a string has no subexpressions.** `replace` finds characters that
match, not occurrences of a variable. There is no amount of cleverness — no word boundaries, no
regular expressions — that recovers the tree from the text, because the text does not record it.

The obvious retreat is to keep the text but let the solver do the thinking: the solver knows
about sorts, after all. But that only moves the bug, and it moves it somewhere expensive to
debug. Take the figure of the paper's §2.1 at its word — one grammar, in which `0 <= v` and
`v + 1` and `3` are all "predicates" — and transcribe it literally:

```lean
inductive Expr where
  | var  (x : String)
  | int  (n : Int)
  | bool (b : Bool)
  | bin  (l : Expr) (op : String) (r : Expr)
  | and  (l r : Expr) | or (l r : Expr) | not (l : Expr)
  | ite  (c t e : Expr)
  | app  (f : String) (args : List Expr)
```

Nothing in that grammar stops us building the conjunction of a comparison and the number 3, and
the printer is happy to hand it to us:

```lean
def ok    : Expr := .and (.bin (.int 0) "<=" (.var "v")) (.bin (.var "v") "<" (.app "len" [.var "xs"]))
def junk  : Expr := .and (.bin (.int 0) "<=" (.var "v")) (.int 3)
def junk2 : Expr := .ite (.bin (.int 0) "<" (.var "x")) (.int 3) (.bool true)

#eval ok.pp      -- the formula we wanted
#eval junk.pp    -- a conjunction whose right operand is the number 3
#eval junk2.pp   -- an ite with branches of two different sorts
```

```
$ lean book/code/ch02/one-grammar.lean
"((0 <= v) && (v < len(xs)))"
"((0 <= v) && 3)"
"if (0 < x) then 3 else true"
```

Feed the second to z3, in the form a string-based checker would emit:

```
$ cat book/code/ch02/junk.smt2
(declare-const v Int)
(assert (and (<= 0 v) 3))
(check-sat)

$ z3 -smt2 book/code/ch02/junk.smt2
(error "line 2 column 23: Sort mismatch at argument #2 for function (declare-fun and (Bool Bool) Bool) supplied sort is Int")
sat
$ echo $?
1
```

Read that transcript twice. The first line is our bug, reported by someone else. The second
line is the one that should worry you: **z3 said `sat` anyway.** A checker that reads the first
line of stdout and ignores stderr accepts a query the solver refused to parse — and the program
it just "verified" is verified against nothing. (So the Ch 3 solver will read both streams and
treat an `(error …)` as a hard failure, never as `unsat`.)

So the chapter has two problems, and they have one solution. Substitution needs substructure,
and the AST needs to know which nodes are formulas. Predicates have to be data.

The four programs this chapter runs are in [book/code/ch02/](code/ch02) —
[predicate-as-string.lean](code/ch02/predicate-as-string.lean),
[one-grammar.lean](code/ch02/one-grammar.lean),
[map-version.lean](code/ch02/map-version.lean), [derive.lean](code/ch02/derive.lean) — and
[junk.smt2](code/ch02/junk.smt2). Every transcript below is their output, copied. Each is
self-contained: `lean` one of them directly, no Lake and no wait. The book shows the interesting
lines; the files hold the boilerplate around them.

**Deliverable:** [Sprite/Refine.lean](../Sprite/Refine.lean) — 268 lines, four inductives,
eleven definitions, thirteen tests. **Gate:**

```sh
lake build                       # green
grep -c '^example' Sprite/Refine.lean   # 13
```

## The grammar, and the one place we leave it

Figure 2.1 of the paper gives the syntax of the refinement logic:

```
predicates  p, q ::=  x, y, z, …        variables
                     | true, false      booleans
                     | 0, -1, 1, …      numbers
                     | p₁ ⋈ p₂          interpreted operators
                     | p₁ ∧ p₂
                     | p₁ ∨ p₂
                     | ¬p
                     | if p then p₁ else p₂
                     | f(p̄)             uninterpreted function
```

The faithful transcription is the one we just watched produce `((0 <= v) && 3)`. The figure is
not wrong — §2.1 says the predicates come from QF-UFLIA, and in a many-sorted logic every
expression has a sort, so `((0 <= v) && 3)` is simply not a formula; the figure just doesn't
say who checks. We check, and we do it by splitting the figure's one grammar into two types:

```lean
inductive Arith where
  | add | sub | mul

inductive Rel where
  | eq | lt | le | gt | ge

inductive Term where
  | var   (x : String)
  | int   (n : Int)
  | bool  (b : Bool)
  | arith (o : Arith) (l r : Term)
  | app   (f : String) (args : List Term)

inductive Pred where
  | tru   : Pred
  | fls   : Pred
  | rel   (op : Rel) (l r : Term) : Pred
  | holds (t : Term) : Pred
  | and   (p q : Pred) : Pred
  | or    (p q : Pred) : Pred
  | not   (p : Pred) : Pred
  | ite   (c p q : Pred) : Pred
```

`⋈` has been split twice, into `Arith` (which returns an integer) and `Rel` (which returns a
truth value), because every consumer downstream dispatches on that difference: the emitter of
Ch 3 writes `+` into a term and `<=` into a formula, and the qualification heuristic of Ch 13
mines only the latter.

Three constructors deserve a word.

**`Pred.holds`** is the constructor the figure does not have, and it is the price of the split.
A boolean-valued *term* can stand as a formula, and the corpus does exactly that:
`test/L3/neg/abs01.re` opens with

```re
/*@ val cassert : bool[b|b] => int */
```

where the refinement of `b` is `b` itself — "this boolean is true". In the single-grammar
version that is just an `Expr` in predicate position; here it is an explicit coercion from
`Term` to `Pred`, written once, and every other integer in a formula position is a type error
the compiler catches at the construction site rather than in z3's stderr.

**`Term.bool`** sits on the other side of the same bridge: `true` is a term (it can be compared,
`b == true`), and `Pred.tru` is the formula. Two constructors, one for each sort, and no
ambiguity about which is which.

**`Pred.ite`** survives although `(c ⇒ p) ∧ (¬c ⇒ q)` says the same thing. Ch 11's path-sensitive
typing produces ite-refinements directly; unwinding the abbreviation into implications makes
both the query and the error message bigger, and §2.1 keeps it for the same reason.

The AST carries **no sorts**. `var "x"` says `x` and nothing else; `app "len" [x]` says `len`
takes one argument and stops there. The reference implementation does the same — its `Reft` is a
symbol plus a fixpoint `Expr`, and the sorts live in a separate `IEnv` — and it buys two things.
The first is the definition below: `subst` is total on syntax with no side conditions, because
there are no sorts to disagree with. The second is that Ch 7's kind checker gets to be a
*checker* — a pass that reports "the refinement `x : s → t` mentions `x`, which has function
sort" — rather than being precluded by the representation. When a language cannot express a
malformed program, its type checker cannot report it.

## Printing

The printer is user interface: every `#eval` in this book, every type error the checker reports,
and every file in `test/golden/` shows a predicate through it.

```lean
def Term.pp : Term → String
  | .var x       => x
  | .int n       => if 0 ≤ n then toString n else "(" ++ toString n ++ ")"
  | .bool b      => toString b
  | .arith o l r => "(" ++ l.pp ++ " " ++ o.symbol ++ " " ++ r.pp ++ ")"
  | .app f args  => f ++ "(" ++ Term.ppList args ++ ")"

def Pred.pp : Pred → String
  | .tru       => "true"
  | .fls       => "false"
  | .rel o l r => "(" ++ l.pp ++ " " ++ o.symbol ++ " " ++ r.pp ++ ")"
  | .holds t   => t.pp
  | .and p q   => "(" ++ p.pp ++ " && " ++ q.pp ++ ")"
  | .or p q    => "(" ++ p.pp ++ " || " ++ q.pp ++ ")"
  | .not p     => "~(" ++ p.pp ++ ")"
  | .ite c p q => "if " ++ c.pp ++ " then " ++ p.pp ++ " else " ++ q.pp
```

Every compound subexpression gets parentheses, so the output is noisy and unambiguous:

```
$ lake build
info: Sprite/Refine.lean:230:0: "((0 <= i) && (i < len(xs)))"
info: Sprite/Refine.lean:231:0: "(0 <= v)"
info: Sprite/Refine.lean:232:0: "(0 < v)"
```

A precedence-aware printer would drop most of those parentheses; it is twenty lines, a table of
levels, and one more thing to keep in sync with the parser of Ch 6. We take the noise instead,
because then `parse (pp p) = p` holds by construction rather than by argument: each pair of
parentheses marks exactly where an ambiguity would otherwise live. When the golden files of
Ch 10 start hurting the eyes, the challenge's cousin — a minimal-parenthesis `pp` — is the fix,
and it is a purely local change.

The surface syntax is fixpoint's, not Lean's: `&&`, `||`, `~`, `==`, `<=`. It has to match what
the corpus actually says, and the corpus hedges on one operator: `[v|v = x + y]` and
`[v | v == x + 1]` both appear. We print `==` and Ch 6's parser will accept either spelling.
Negative integers keep their parentheses — `(0 + (-1))` re-parses, `0 + -1` is not a term.

## Substitution

The paper's `p[x := q]`, in the same order the paper writes it:

```lean
def Term.subst (t : Term) (x : String) (s : Term) : Term :=
  match t with
  | .var y       => if x == y then s else .var y
  | .int _       => t
  | .bool _      => t
  | .arith o l r => .arith o (l.subst x s) (r.subst x s)
  | .app f args  => .app f (Term.substList args x s)

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
```

Every later chapter calls this. Ch 4 uses it at each application, to read the result refinement
off a function's type (`size`'s `v = len(x)` becomes `v = len(xs)` at a call `size(xs)`); Ch 12
uses it to instantiate an inferred `?r`; Ch 13 qualifies the results; Ch 21 needs it to state
what validity even means.

Note what is *not* in the definition: no freshness check, no renaming, no side condition. The
paper's parenthetical — "(capture avoiding)" — is doing no work here, for one reason: **`Pred`
has no binders.** `ite` binds nothing; `holds` binds nothing; so no free variable of `s` can be
captured by anything in `p`. That is a property of this AST on this day, and not a property of
substitution. When Ch 12 adds the quantifier of a constraint, `Pred.forall x p`, the function
above becomes wrong, and the tests below stop being `rfl`. We will meet that bug in the
challenge rather than in Chapter 12, where it costs a debugging session.

## Recursion the kernel can check

The `app` case above calls `Term.substList`, a helper that looks like ceremony. Why not write
the natural thing?

```lean
  | .app f args  => .app f (args.map (fun a => a.subst x s))
```

It works. It computes. It is also unverifiable:

```lean
#eval (Term.app "len" [Term.var "x"]).substMap "x" (Term.int 1)
#reduce (Term.app "len" [Term.var "x"]).substMap "x" (Term.int 1)
```

```
$ lean book/code/ch02/map-version.lean
Sprite.Term.app "len" [Sprite.Term.int 1]
Acc.rec
  (fun x₁ h ih =>
    Term.rec
      (fun x x_1 x_2 s =>
        Bool.rec (motive := fun x_3 => x_3.Reflects ((x_2 == x) = true) → Term) (fun h => Term.var x) (fun h => s)
          (Bool.rec (motive := fun x_3 =>
              x_3.Reflects (x_2.1.1.toList = x.1.1.toList) →
⋯
```

Eighty-two lines, and no constructor at the end of it — the `"x"` and the `Term.int 1` are
still sitting there as *arguments* to a recursor the kernel cannot open. A `map` whose function
is itself recursive is not structurally recursive as far as Lean is concerned, so the equation
compiler falls back to well-founded recursion, and the resulting `Acc.rec` is opaque to the
kernel's evaluator. `#eval` runs compiled code and is happy; `rfl`, `decide`, and every
`induction` you will attempt in Part III are not. Writing the `List` recursion out by hand, in a
`mutual` block with the function it serves, gets structural recursion back — and with it `rfl`,
and with it the ability to prove anything about these functions later. `partial` is the other way
out and is not on the table: it terminates by fiat, and the linter is watching.

The same applies to `Term.ppList`, for the same reason.

## What we cannot derive

Chapter 1 derived `BEq` and compared with `==`. The natural next step — `deriving DecidableEq`,
so the tests can be `by decide` instead of `rfl` — fails, and the way it fails is worth knowing:

```
$ lean book/code/ch02/derive.lean
derive.lean:8:22: error: None of the deriving handlers for class `DecidableEq` applied to `Term`
derive.lean:14:22: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  Decidable (a✝¹ = b✝¹)
…
'Sprite.instDecidableEqPred' depends on axioms: [sorryAx]
```

(The `…` is two more copies of the same instance failure — one per field of `Pred` that holds a
`Term`.)

`Term` cannot derive it: the `args : List Term` field needs `Decidable (xs = ys)` for lists of
`Term`, which needs the instance it is in the middle of deriving, and the handler gives up
rather than build one. `Pred`, whose fields include `Term`, then half-succeeds: the deriving
handler emits an instance anyway, and that instance's `decEq` is `sorry`. The last line above is
`#print axioms` catching it — which is exactly the audit standing rule 6 promises to run on
Part III, catching a `sorry` nobody wrote. Take the lesson early: a derived instance is code,
and code has to be checked.

So [Sprite/Refine.lean](../Sprite/Refine.lean) derives `Repr` and nothing else, for the one
thing that needs it: `#eval`. Not `BEq` — nothing in this file compares two predicates with
`==` — and not `Ord` or `Hashable`, though both derive fine. Chapter 1 derived `BEq` because its
`#guard`s use it; when the subtyping cache of Ch 8 needs to key a dictionary on a predicate, the
derivation goes in with the code that calls it. A deriving clause nobody calls is a promise you
have not tested, and this file has already met an untested derived instance that turned out to be
`sorry`.

## What the machine said

```
$ rm .lake/build/lib/lean/Sprite/Refine.olean && time lake build
ℹ [10/11] Built Sprite.Refine (340ms)
info: Sprite/Refine.lean:230:0: "((0 <= i) && (i < len(xs)))"
info: Sprite/Refine.lean:231:0: "(0 <= v)"
info: Sprite/Refine.lean:232:0: "(0 < v)"
Build completed successfully (11 jobs).

real    0m0.725s

$ grep -rn "sorry\|admit\|blasterProven" Sprite/ ; echo "exit=$?"
exit=1

$ lake exe sprite --version
sprite 0.1.0
```

The `#eval` lines are Lean's, not typed in by hand. The grep is standing rule 5 and finds
nothing (`exit=1` is grep's "no matches"). And Chapter 1's CLI still builds, because everything
in this chapter is data and nothing in it is wired to anything yet.

`linter.all` did bite, once, and the way it bit is worth recording: it wants a docstring on
*every public constructor*, which is twenty-one docstrings we had not planned to write:

```
error: Sprite/Refine.lean:79:4: missing doc string for public constructor Pred.tru
```

We kept them, because for an AST the constructor docstring *is* the specification — `Term.var`'s
one-line docstring ("A variable, `x`. Unsorted: the checker's environment says what `x` is.")
answers the question a reader of the figure has, in the place she asks it. The two-line
docstrings on `Arith.add` and friends read like a manpage, and that is fine; the ones on
`Pred.holds` and `Pred.ite` are doing real design work.

## Tests

Thirteen `example`s at the bottom of the file. The three that carry the chapter:

```lean
example : (index "i" "xs").pp = "((0 <= i) && (i < len(xs)))" := rfl

example : (index "i" "xs").subst "i" (.app "len" [.var "ys"])
          = Pred.and (.rel .le (.int 0) (.app "len" [.var "ys"]))
              (.rel .lt (.app "len" [.var "ys"]) (.app "len" [.var "xs"])) := rfl

example : (Pred.holds (.app "is-nil" [.var "xs"])).pp = "is-nil(xs)" := rfl
```

`index` is `0 <= i && i < len(xs)` — the formula from the opening of the chapter, now a
`def` so the tests, the prose, and Chapter 3's two SMT queries all name the same object.

Each test is `rfl`: the kernel itself evaluates `pp` and `subst` and compares two constructor
trees. No instance, no `decide`, nothing run and trusted. This is why the section on recursion
matters — with the `map` version, `rfl` fails on `Acc.rec` and the honest fallback is a
`#guard` that *runs* the comparison at elaboration time and panics on failure. Chapter 1's CLI
tests are `#guard`s, and that is right for a function returning `String`; here we can afford the
real thing.

The second test above is the one the string version failed: the `xs` under `len` is untouched
when `i` is substituted, because substitution walks *nodes* and `xs` is not the node named `i`.
Two of the other thirteen exist only to make that distinction visible — `((0 <= i) && b)` and
`((0 <= i) && (i < len(xs)))` are different formulas that a text-based checker has no way to
tell apart.

These tests are shadows. Each one becomes a universally quantified theorem in `Spec/` around
Ch 22 — `subst` of a fresh variable is the identity, two substitutions compose, printing is
injective on the fragment we print — and the point of writing them now, in the cheap form, is
that when the theorems arrive we will already know which ones are true.

## Design discussion

**Two types, not one, and not four.** The alternatives to `Term`/`Pred` were: the figure's
single grammar, and a fully two-sorted pair (`ITerm`/`BTerm`, integer- and boolean-valued
terms, with `Pred = BTerm`). The single grammar pushes every sort error to the solver, where it
arrives as the transcript at the top of this chapter; it also forces the semantics of Ch 21 to
evaluate nonsense, so `Satisfies` would need either an `Option`-returning evaluator or a
well-formedness hypothesis on every clause. Four types rule out every ill-sorted term at
construction — but they make `subst` painful, because substituting a boolean-valued term for a
variable in an integer-valued term must be rejected *by the type*, which means the type has to
be in the term, which is the sorts-in-the-AST decision we just refused. Two types is the point
where the category errors — a formula where an integer goes, an integer where a formula goes,
the two that a string checker commits daily — become unrepresentable, and the remaining
fine-grained sort errors stay where they can be *reported*: Ch 7.

**Names are `String`.** The reference uses fixpoint's interned `Symbol`, and every comparison in
`subst` is then a pointer compare. We pay `O(n)` on each of what are, at this scale, short
comparisons of short names, and we do not write an interning table, a fresh-name supply, or a
`Show` instance that decodes into something a human can read in a golden file. Ch 8's subtype
cache will want a dictionary keyed on pairs of types, and if `String` keys turn out to be slow
the fix is one `Ord` derivation and a `Name` type, both local to the cache.

**No source spans yet.** The reference threads a phantom label `a` through every constructor —
`EVar !F.Symbol a`, `EFun !(Bind a) !(Expr a) a` — so that every subexpression can point back at
the file. We add spans in Ch 5, where the lexer starts producing them, and we will pay for the
decision exactly once: adding a parameter to four inductives is a compile error at every
construction site, and the compiler will enumerate them for us. Deferring is cheap when the
machine keeps the list.

**Why `Rel` keeps `gt` and `ge`.** They are `lt` and `le` with arguments swapped. Normalizing at
construction would shrink the AST and enlarge the error messages: the user who wrote
`x >= 0` wants to read `x >= 0` back, and Ch 3 wants to emit SMT-LIB's `>=` rather than a `Not`
node z3 has to undo. Redundancy in a surface AST is cheap; the normalized form is a Ch 15
question, when monomorphization starts rewriting types anyway.

**No `⇒` on `Pred`.** The figure's predicates have no implication — only constraints do
(`∀x:b. p ⇒ c`), and a constraint's implication is not a `Pred`: it cannot appear under a `¬`, it
has no truth value of its own, and Ch 3 flattens it into `p ∧ ¬q` before the solver sees it.
Adding it to `Pred` "for convenience" would add a constructor that the emitter has to case-split
on and the kind checker has to reject in three positions. If Ch 12 wants it, it gets its own
type, which is what `Constraint` is for.

## Challenge

**Capture (**). The paper writes "(capture avoiding)" and this chapter's `subst` ignores it,
because nothing binds. Give `Pred` a binder:

```lean
  | forall (x : String) (p : Pred) : Pred
```

and extend `Pred.subst` to match. Now take the formula the chapter already has, bound at its
own value variable:

```lean
def bad : Pred := .forall "v" (index "v" "xs")      -- ∀v. (0 <= v) && (v < len(xs))
#eval bad.subst "xs" (.var "v")
```

Print the result and find the variable that changed meaning. Fix `subst` by renaming the bound
variable to something fresh when the substitution would capture it — a `rename : String → Pred →
Pred` and a fresh-name supply are enough; the usual trick is to keep the counter in the checker's
monad, which Ch 9 will have anyway.

Two things to write down in `NOTES.md` before you move on: the exact formula that exposed the
bug, and the side condition you now need in order to state "`subst` of a fresh variable is the
identity". That side condition is the hypothesis Ch 22's `subst_id` will not let you discharge
without it, and you have just discovered it by hand instead of by `omega` failing at 1am.

*** extension: normal form (**). Write `Pred.nnf : Pred → Pred` pushing `not` down to the atoms,
so `~(a && b)` becomes `~a || ~b` and `~if c then p else q` becomes
`if c then ~p else ~q`. Ch 3 needs it: every query is `p ∧ ¬q`, and negating a formula we could
have kept positive is how you hand z3 a formula twice the size it needs. The interesting case is
`not (rel …)` — you have no `≠` in `Rel`, so `~(a == b)` has to stay a negated atom, which is
exactly what a *literal* is. Check that `nnf` is idempotent on every formula in this
chapter's tests, and note which of them it actually changes.

## Inspiration

- *Refinement Types* §2.1–§2.3 — the figure, the definition of validity, and §2.3's argument
  for quantifier-free predicates. Read §2.3 twice: it is the reason we are allowed to trust a
  solver's answer, and it is short.
- *Crafting Interpreters*, ch. 4 "Trees and Expressions" — Nystrom makes exactly this chapter's
  move, from a token soup to a grammar-shaped AST, for exactly this reason: the representation
  has to carry the structure the later phases need. Read it as the same bug report, filed by
  someone else eight years earlier.
- `Language/Fixpoint/Types.hs` in liquid-fixpoint, the reference's dependency — look at `RRProp`
  and at how sorts live in `IEnv` rather than in the expression. The `Reft` is `(Symbol, Expr)`:
  a value variable and a predicate, which is the pair Ch 4 will name.

## Notes for `NOTES.md` (the errors this chapter actually produced)

1. `deriving DecidableEq` on `Term` — the `List Term` field makes the handler refuse; on `Pred`
   it half-succeeds and emits an instance whose `decide` is `sorry`. `#print axioms` catches it.
2. `args.map (fun a => a.subst x s)` — well-founded recursion, `Acc.rec`, no `rfl`. Fixed by the
   mutual `Term.substList`/`Term.ppList`.
3. `mutual` after a docstring — `unexpected token 'mutual'`. The docstring has to sit on the
   `def` *inside* the block, not on `mutual`.
4. Dotted notation in a goal's right-hand side — `.arith` on its own is ambiguous against
   `Lean.Meta.Simp.Config.arith`; the expected type is not yet known there. Spell `Term.arith`
   and `Pred.ite` in the `example` statements.
5. Three of the thirteen tests were wrong the first time, all of them printing tests, all
   missing the outer parentheses `Pred.and` adds. The `#eval` that was already in the file said
   so; the fix was to read it.

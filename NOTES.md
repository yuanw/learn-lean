# NOTES

Every wall, what Lean said, and what unblocked it. Standing rule 7: Chapter 24's prose is made
of these entries, so they are written for a reader who has not hit the wall yet.

## Ch 2 — Predicates (≈3 h of wall time, ~40 min of it Lean's fault)

The AST and the printer were an hour. The rest went to two things this entry exists to
record: `deriving DecidableEq`, and recursion over a `List` field.

### `deriving DecidableEq` leaves a `sorry` behind

Wanted `DecidableEq` on the AST so the tests could be `by decide`.

```
error: None of the deriving handlers for class `DecidableEq` applied to `Term`
```

`Term`'s `args : List Term` field needs `DecidableEq Term` to build `DecidableEq (List Term)`,
which is the instance being derived, so the handler refuses. Fine — that is an honest failure.

Not fine: deriving it on `Pred` (whose fields mention `Term`) *half-succeeds*. It emits an
instance, and the instance's `decEq` is `sorry`:

```
'Sprite.instDecidableEqPred' depends on axioms: [sorryAx]
```

`decide` then fails loudly ("reduction got stuck at `sorry`"), so you find out — but only if you
try to *use* the instance. A file that derives it and never calls `decide` compiles clean and
ships an unsound equality test. The build's `warningAsError` did not flag it, because no
declaration written by me used `sorry`.

Unblocked by: `#print axioms` on the instance, which is standing rule 6 pointed at generated
code instead of at my theorems. Dropped `DecidableEq` — and then `BEq` too, once it was clear
nothing in the file compares two predicates. Only `Repr` stays, because `#eval` needs it.

### `args.map f` is not structural recursion

`Term.subst` with `| .app f args => .app f (args.map (fun a => a.subst x s))` compiles, and
`#eval` gives the right answer. `#reduce` gives 18 lines of `Acc.rec` and no answer, and `rfl`
fails to prove `(Term.var "x").subst "x" (Term.int 1) = Term.int 1`.

Cause: a `map` whose function is the recursively-defined one defeats the structural recursion
check, so the equation compiler goes well-founded; `Acc.rec` is opaque to the kernel evaluator.

Tried and rejected:
- `partial def` — terminates by fiat, and `warningAsError` makes the `partial` warning an error.
- `by native_decide` in the tests — `native_decide` needs `Decidable` for the Prop (we have
  none) and leaves `Lean.ofReduceBool` in the axiom set, which rule 6 forbids anyway.
- raising `maxRecDepth` — irrelevant; the reduction is stuck, not deep.

Unblocked by: writing the list recursion out, `mutual` with the function it serves
(`Term.substList`, `Term.ppList`). Structural again, no axioms at all
(`#print axioms Sprite.Term.subst` → *does not depend on any axioms*), and all thirteen tests
close with `rfl`.

This is also why `partial` and `Termination_by` do not appear anywhere in `Sprite/`: Part III
has to do `induction t` on these types, and an `Acc.rec`-based eliminator makes that a different,
worse problem.

### The three tests that were simply wrong

All three were printing tests, all three forgot the outer parentheses that `Pred.and` adds:
`(0 <= i) && (i < len(xs))` instead of `((0 <= i) && (i < len(xs)))`. Lean's message is
`Type mismatch / rfl has type ?m.3 = ?m.3`, which says nothing useful. The `#eval` of the same
formula, already in the file two lines above, said exactly what was wrong.

Lesson kept: print the formula before you assert what it prints as.

### Linter notes

`linter.all` + `warningAsError` demanded a docstring on all 21 public constructors, and rejected
a docstring placed before `mutual` (`unexpected token 'mutual'` — it has to sit on the `def`
inside the block). Dotted notation on the right of `=` in an `example` (`= .arith …`) fails
because the expected type is not known yet there; spell the constructor out.

### Deliberate limits left in place

- `Arith` has no `div`/`mod`/set/string operators. No corpus file uses one; marked `shortcut:`.
- No `BEq`/`Ord`/`Hashable` on the AST: nothing compares two predicates yet. Goes in with the
  Ch 8 cache that needs it.
- No source spans in the AST. Ch 5 adds them; the compile errors will enumerate the sites.
- No `Ord`/`Hashable` derivations until Ch 8's subtype cache asks for keys.

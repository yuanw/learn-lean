# Crafting Refinements

A self-paced tutorial in the style of *Crafting Interpreters*: we build a refinement type
checker for the language of Jhala & Vazou's *Refinement Types* (arXiv:2010.07763) in Lean 4,
one chapter at a time, and then — Part II — we prove things about what we built.

The artifact is not just a program. It is `book/`, a written tutorial with real console
output, design discussions, and challenges, that happens to contain a working checker.

---

## Fixed decisions

| | |
|---|---|
| Host language | **Lean 4** `v4.35.0`, via the existing nix flake (`leanPackages`) |
| Object language | **sprite** — the paper's eight languages λ, λβ, λκ, λα, λδ, λρ, λτ, λπ |
| Surface syntax | sprite's `.re` files, annotations in `/*@ ... */` comments (keeps the reference corpus usable verbatim) |
| CLI | `lake exe sprite <level> <file>` mirroring `stack exec -- sprite 8 test/L8/pos/listSet.re` |
| Solver | **z3 5.3.2** from nixpkgs, `pkgs.z3` in `devShells.default.packages`; subprocess + SMT-LIB text we emit ourselves |
| Reference impl | `/tmp/sprite` (clone of `ranjitjhala/sprite-lang`) — read-only oracle, and the source of the 113-file test corpus |
| Not used in proofs | `Blaster`'s `blaster` tactic (it closes goals with `axiom blasterProven`, i.e. an admit). Allowed as a *counterexample oracle* only. See the audit rule below. |

Rename freely. Everything below survives a rename of `sprite` except the test-corpus paths.

---

## Repo layout

```
learn-lean/
  Sprite/
    Refine.lean        -- Pred, Pred semantics, substitution      (Ch 2, 21)
    Smt/
      Emit.lean        -- Pred → SMT-LIB text                      (Ch 3)
      Solver.lean      -- z3 subprocess, counterexample parsing     (Ch 3)
    Syntax/
      Ast.lean         -- Base, Type r, Prim, Expr                 (Ch 4)
      Print.lean       -- pretty printer                           (Ch 4)
      Scan.lean        -- tokens, /*@ */ handling                  (Ch 5)
      Parse.lean       -- recursive descent                        (Ch 6)
    Check/
      Kind.lean        -- well-formedness                          (Ch 7)
      Sub.lean         -- subtyping as an oracle call              (Ch 8)
      Ctx.lean         -- environments, templates                  (Ch 9)
      Dep.lean         -- the declarative checker                  (Ch 9-10)
      Branch.lean      -- λβ                                       (Ch 11)
      Constrain.lean   -- Horn VCs                                 (Ch 12)
      Fix.lean         -- fixpoint + qualification                 (Ch 13)
      Poly.lean        -- λα                                       (Ch 14)
      Data.lean        -- λδ datatypes + measures                  (Ch 16-17)
      RPoly.lean       -- λρ                                       (Ch 18)
      Term.lean        -- λτ metrics                               (Ch 19)
      Reflect.lean     -- λπ                                       (Ch 20)
    Main.lean          -- CLI + corpus runner                      (Ch 10)
  Spec/                -- Part II: the Prop-side twin of Sprite/
    Semantics.lean     -- satisfaction, validity                   (Ch 21)
    Typing.lean        -- HasType as an inductive relation         (Ch 25)
    Sound.lean         -- VC generation is sound                   (Ch 24)
  book/
    01-....md          -- one markdown file per chapter
  test/
    L1/ ... L8/        -- copied verbatim from the reference repo, pos/ and neg/
    golden/            -- expected checker output per file
  PROOFS.md            -- every theorem you proved, one English sentence each
  NOTES.md             -- every failure you got stuck on, and why
```

One git tag per chapter: `git tag ch-03-oracle`. The tutorial is read by diffing tags, the
way CI's readers diff chapters.

---

## The chapter grammar

Every chapter has the same six parts. If a part is empty, the chapter is wrong.

1. **The problem.** Opens with a program the checker rejects (or accepts) when it shouldn't.
   Not a feature list — a bug report from yourself.
2. **The code.** Grows `Sprite/` in front of the reader. Include the version that *failed*
   and the error text. Deliberate wrong turns are the curriculum, not noise.
3. **What the machine said.** Real terminal output: the `lake exe` run, the `.smt2` it wrote,
   z3's `sat`/`unsat`, the counterexample. Copy-paste, never invented.
4. **Design discussion.** The CI section. Alternatives considered, why this one, what it
   costs, what it buys. This is where the paper's footnotes (§3.3.3's "why arguments are
   variables", §2.3's "why quantifier-free") get answered in your own words.
5. **Challenge.** One deep exercise, not five shallow ones. Asterisked difficulty:
   `*` ~20 min, `**` ~1 h, `***` an afternoon.
6. **Inspiration.** Two or three things to read, with one line each on why.

Tag every chapter `[impl]`, `[proof]`, or `[both]`. The two threads braid — never two
`[impl]` chapters in a row past Ch 13.

---

## Part 0 — Orientation

| Ch | Title | Opens with | Deliverable | Gate | h |
|---|---|---|---|---|---|
| 1 | What a refinement checker owes you | `let six : nat = 6` — why should a *type* know 6 ≥ 0? | flake carries `pkgs.z3`; `lake exe sprite --version`; corpus copied | `lake build` green, `sprite --help` prints | 2 |
| 2 | Predicates | write `0 ≤ v ∧ v < length(x)` as data, not text | `Sprite/Refine.lean`: `Pred` AST (Fig 2.1), printer, `subst` | `#eval` prints the formula back; 10 `example`s | 4 |
| 3 | The oracle | two VCs, one valid one not, and no way to tell | `Smt/Emit.lean` + `Smt/Solver.lean`; `.liquid/` output; `isValid : List String → Pred → IO Bool` | paper's §2.2 pair: `∀x. 0≤x ⇒ 0<x+1` → valid; `length` version → falsified with `length ↦ 0` | 4 |

Ch 3 is the "first program runs" chapter. Do not skip it or defer it to Ch 12: the whole
tutorial hangs on seeing z3 answer a question you asked.

## Part I — A checker for one small language

| Ch | Title | Opens with | Deliverable | Gate (corpus) | h |
|---|---|---|---|---|---|
| 4 | Terms and types | `inc`'s type mentions its argument's name — so binders are in the AST | `Syntax/Ast.lean` (Fig 3.1/3.2), `Print.lean` | print-parse round trip on 5 hand-built terms | 4 |
| 5 | Scanning `.re` | the annotation lives in a *comment*, so the lexer must care | token list, `/*@ */` capture, source spans | golden token dumps | 3 |
| 6 | Parsing | `"2 + 3 * x"` parses as `(2+3)*x` in your checker — wrong | recursive descent, precedence, `let`/`lam`/app/annotation | all 9 `test/L1` files parse | 5 |
| 7 | Kinds and well-formedness | `int{x : 0 ≤ x}` is fine, `x : s → t` refined is not | `Check/Kind.lean`: `B` / `★`, free-variable check on refinements | 6 new negatives rejected before the solver is ever called | 3 |
| 8 | Subtyping is an oracle call | `{v : 0 ≤ v}` ⊴ `{v : 0 < v}`? Ask z3 | `Check/Sub.lean`: `subType Γ t s → m [VC]`; caching | unit tests on 12 subtype pairs | 4 |
| 9 | Contexts and the declarative rules | the paper's Fig 3.3 rules, typed out as Lean data | `Check/Ctx.lean`, `Check/Dep.lean` for `let`/`lam`/app/const | 4 of 9 `test/L1/pos` | 6 |
| 10 | End-to-end, and a test harness | `#guard` can't fork a process, so what tests a checker? | `Sprite/Main.lean` CLI; `golden/` diffing; exit codes | **all 9 `test/L1`** incl. the 4 `neg` | 4 |
| 11 | Branches: path sensitivity | `if x > 0 then 1/x else 0` — the checker must reason *per path* | λβ: `ite` typing, assumption accumulation | **10 `test/L2`** | 5 |
| 12 | `?`-refinements | nobody will write `x:int{v:0≤v ∧ v<x+1}` by hand | `Check/Constrain.lean`: templates, `KVars`, Horn VC generation | VCs for `test/L3` match reference `.liquid/*.smt2` | 6 |
| 13 | The fixpoint loop | your generated constraints have `∀` you can't ground | λκ: instantiation loop, **qualification**, k-limit, timeout | **11 `test/L3`** | 8 |

Ch 13 is the first place the reference implementation is worth reading line by line — the
qualification heuristic (`Qualifiers.hs` / `Prims.hs`) is not guessable.

## Part II — Growing the type system

| Ch | Title | Opens with | Deliverable | Gate | h |
|---|---|---|---|---|---|
| 14 | Type polymorphism | `id`'s refinement can't mention a type variable's value | λα: `∀α. t`, instantiate/abstract | **10 `test/L4`** | 5 |
| 15 | Sorts, monomorphization, defunctionalization | `∀f : int → int. ...` is not first-order | sort assignment; higher-order args become `f_k` + axioms | Ch 13's loop still green on new queries | 5 |
| 16 | Data types | `List` whose `nil` has length 0 — a *refined constructor* | λδ: `data` decls, `is`-tests, constructor refinements | 6 of 29 `test/L5` | 6 |
| 17 | Measures | `length (cons x xs) = 1 + length xs` is not free — congruence isn't automatic | recursive functions → UF + **axiomatized equations** in the query | **29 `test/L5`** | 7 |
| 18 | Refinement polymorphism | `map` on `list{n:0≤n}` vs `list{v:v=length xs}` | λρ: `rabstract`/`rslice`, the `RType` kind | **22 `test/L6`** | 8 |
| 19 | Termination | `loop n = loop n` type-checks. That's a hole. | λτ: `metric`, lexicographic tuples, decreasing VCs | **14 `test/L7`** | 7 |
| 20 | Reflection: programs as proofs | can your language prove its own `append` theorem? | λπ: `spec`, `rall`, proof terms as `let`s, `Reflect.hs` equivalent | **8 `test/L8`** | 8 |

## Part III — Proving (the mirror)

Part I gave you an *executable* checker returning `Bool`/`Except`. Part III builds the
*declarative* twin in `Spec/` as inductive `Prop`s and proves they agree — CI's two
implementations, one fast and one trustworthy.

| Ch | Title | Theorem you prove | Why it hurts | h |
|---|---|---|---|---|
| 21 | What a predicate means | `Satisfies : Env → Pred → Prop`, `Valid` | defining truth for your own syntax without leaking Lean's | 4 |
| 22 | Substitution | `subst_id`, `subst_subst` (commutation, freshness side conditions) | the freshness hypotheses you "didn't need" until Ch 24 | 5 |
| 23 | The emitter is faithful | `Smt.ok (emit p) ↔ Satisfies env p` — z3's answer matches your semantics | you'll find an emitter bug here; that's the point | 6 |
| 24 | VC generation is sound | `genVCs e = cs → Valid cs → HasType [] e t` | the main theorem; needs Ch 22's lemmas generalized over context, env, stack | 10 |
| 25 | Progress and preservation | for the typed λβ fragment; `weakening` and `substitution` discovered, not given | IH ordering on `Step`; "no constructors apply" | 8 |
| 26 | The axiom audit | what you actually assumed: `#print axioms` on every `PROOFS.md` entry | discovering a theorem quietly depended on `Classical.choice` — or worse | 3 |

Ch 24 is the reason the project exists. Budget for it to fail twice.

## Appendices

- **A. Error messages.** Unsat cores, which annotation caused this failure, the §11 debugging story.
- **B. Capstone menu.** Verified checker completeness / closure conversion / DCE / a `#sprite` macro.
- **C. Challenge solutions.** Only after you've failed on the challenge.
- **D. Reading list.** Per chapter, the paper's §, the Hitchhiker's Guide chapter, the Zulip thread.

**Total ≈ 130 h.** If that's not your life: the trim path is Ch 1–13 + Ch 21–24 (≈ 75 h),
which gets you a working λκ checker and one real soundness theorem. Cut Ch 14–20 and 25–26.

---

## Standing rules

1. **State the general version.** No lemma with a fixed context, environment, or stack.
   The under-generalized IH is the single largest tax on this project.
2. **Attack order:** `rfl` → `decide` → `simp` → `omega` → `grind` → `induction ... generalizing ...`.
3. **`simp only [explicit list]`** from Ch 10 onward. Bare `simp` hides which rewrite closed it.
4. **Tests are golden files, not `#guard`.** Checker runs fork z3; that belongs in
   `lake exe`, compared against `test/golden/`, exit code 0/1.
5. **Before every tag:** `grep -rn "sorry\|admit\|blasterProven" Sprite/ Spec/` must be empty
   except lines marked `-- shortcut: <limit>, <when to upgrade>`.
6. **`PROOFS.md` entries carry their axioms.** `#print axioms thm` output pasted under each.
   Allowed set: `propext`, `Classical.choice`, `Quot.sound`. Anything else is a red flag.
7. **Log the wall-time** in `NOTES.md`: what you tried, what Lean said, what unblocked it.
   Ch 24's failure notes become the chapter's prose.
8. **Read the paper's § first, the reference `.hs` last** — except Ch 13, 15, 18, where the
   reference *is* the specification.

## Style notes (so it reads like CI and not like docs)

- "We", present tense, second person for the reader. One idea per chapter.
- No forward references without a promise: "we explain why in Ch 15."
- Every code block earns its place — if you wouldn't say anything about it, cut it.
- Show the failing version first. The error message *is* the teaching material.
- An epigraph per chapter. Yes, really; it forces you to say what the chapter is about.
- Numbers over adjectives: "113 files, 4 of them negative", not "a good test suite".

## First session (Ch 1, ~2 h)

```sh
# 1. z3 into the dev shell — one line in flake.nix, devShells.default.packages
packages = [ lake lp.lean4 pkgs.z3 ];

# 2. corpus, verbatim from the reference clone
mkdir -p test && cp -r /tmp/sprite/test/L{1..8} test/

# 3. the exe target, and a stub CLI that parses its two args and exits
#    lakefile.lean:  executable sprite where root := `Sprite.Main

lake build && lake exe sprite 1 test/L1/pos/inc00.re   # Ch 1's goal: prints, then fails honestly

git commit -am "ch-01: z3 in the shell, corpus in, CLI stub" && git tag ch-01-oracle
```

Then write `book/01-what-a-refinement-checker-owes-you.md` in the same commit. The prose is
part of the deliverable, not a later chore — you'll never write it later.

# 1. What a refinement checker owes you

*[impl] — 2 h — gate: `lake build` green, `lake exe sprite --help` prints*

> The type systems of modern languages … are the most widely used method for establishing
> guarantees about the correct behavior of software. In essence, types allow the programmer to
> describe legal sets of values for various operations … Unfortunately, well-typed programs do
> go wrong.
>
> — Ranjit Jhala and Niki Vazou, *Refinement Types* §1

## The program that starts everything

Here is a sprite program, in the syntax we will use for the whole book:

```re
/*@ val six : int[v|0 <= v] */
let six = 6;

/*@ val bad : int[v|0 <= v] */
let bad = sub(0, 1);
```

The second line is wrong, and we want to be told so before we run anything. `int[v|0 <= v]` —
written `nat` once we have aliases — is not a type in the sense your compiler uses. It is the
*set* of integers satisfying the *predicate* `0 ≤ v`, where `v` names the value being typed.
The annotation `/*@ val bad : … */` is a contract on the definition below it.

Ordinary type systems can say "this is an `int`". They cannot say "this `int` is non-negative",
so they cannot reject `bad`, cannot tell you that `get(arr, i)` will not go out of bounds, and
cannot promise that `size(arr)` returns the number of elements in `arr`. Refinement types close
that gap by putting a decidable logic inside the type.

What does the checker actually have to decide? Strip away the syntax and there is one
question, asked over and over:

> For every value satisfying the assumption predicate, does the conclusion predicate hold?

That is logical implication between predicates over integers, booleans, uninterpreted functions,
and user-defined data types — undecidable in general. Our escape hatch is the same one every
practical refinement type checker uses: restrict the predicates to a fragment where implication
*is* decidable (quantifier-free linear arithmetic with uninterpreted functions, QF-UFLIA),
translate the question into SMT-LIB, and ask a solver. We will write the translation ourselves
and keep [z3](https://github.com/Z3Prover/z3) as a subprocess.

That is the promise. Nine chapters to a checker that keeps it.

## What we owe ourselves

Two rules for this book, from Chapter 1 on.

**The corpus is the spec.** The paper comes with a reference implementation and 113 test
programs, copied into `test/` today, long before we can check any of them:

| level | language | `pos/` | `neg/` | unlocked in |
|---|---|--:|--:|---|
| 1 | λ | 5 | 4 | Ch 10 |
| 2 | λβ | 5 | 5 | Ch 11 |
| 3 | λκ | 5 | 6 | Ch 13 |
| 4 | λα | 5 | 5 | Ch 14 |
| 5 | λδ | 15 | 14 | Ch 17 |
| 6 | λρ | 14 | 8 | Ch 18 |
| 7 | λτ | 8 | 6 | Ch 19 |
| 8 | λπ | 5 | 3 | Ch 20 |
| | | **62** | **51** | |

`pos/` must type-check, `neg/` must be rejected. 62 accept-only programs would let a checker
that accepts everything pass; the 51 negatives are what make the tests mean something.

**A chapter is done when its gate passes**, and the gate is always a command you can run. This
chapter's:

```sh
lake build                 # green
lake exe sprite --help     # prints usage, exit 0
```

## The toolchain, once

Everything comes from nixpkgs' `leanPackages` via the flake; there is no `elan`, no
`lake update`, and Lake never touches the network. Two things matter for us specifically.

z3 joins the dev shell now, in Chapter 1, even though we do not talk to it until Chapter 3:

```nix
devShells.default = pkgs.mkShell {
  # z3 is the oracle the checker talks to over SMT-LIB text (book/ Ch 3).
  packages = [ lake lp.lean4 pkgs.z3 ];
  …
```

```
$ z3 --version
Z3 version 5.3.2 - 64 bit
```

Get z3 installed once and forget it. The alternative — discovering in Chapter 3 that the solver
isn't there — costs an afternoon of debugging a program that was never wrong.

Second: **the checker imports nothing.** Not Mathlib, not `Lean`. `Sprite/` is plain data over
plain functions, and the payoff is measurable:

```
$ touch Sprite/Cli.lean && time lake build
Build completed successfully (10 jobs).

real    0m0.383s
```

The proofs in Part III will live in `Spec/`, which may import whatever it likes. A thirty-second
import cost on every keystroke is the single biggest threat to a project like this, and it is
avoidable by putting the two halves in two libraries.

One flake quirk to know now: `nix build` builds the *committed* tree, so a brand-new file
invisible to git is invisible to the flake. `lake build` sees the working directory. If
`nix build` says `file: …/source/Sprite` does not exist, commit.

## The linter is part of the prose

Every program in this book is printed, so every program in this book has to read well. That is
enforced by the compiler rather than by intent — `lakefile.lean` gives the `Sprite` targets two
options:

```lean
def lintArgs : Array String := #["-Dlinter.all=true", "-DwarningAsError=true"]

@[default_target]
lean_lib Sprite where
  globs := #[.andSubmodules `Sprite]
  moreLeanArgs := lintArgs
```

and they reappear on the command line of every file it builds:

```
… lean -Dlinter.all=true -DwarningAsError=true Sprite/Cli.lean -o …
```

`linter.all` switches on every linter registered in the compiler; `warningAsError` promotes what
they say to a build failure. The first run over the code above produced seven errors, all of one
kind:

```
error: Sprite/Cli.lean:15:10: missing doc string for public inductive Cmd
error: Sprite/Cli.lean:28:4: missing doc string for public def parseArgs
```

That is the cheapest linter there is to satisfy and the one that matters most here: the docstring
for `parseArgs` is the sentence you would have written in the chapter anyway, and now it lives
next to the code that has to keep matching it. Unused bindings fail too, which is the linter
that earns its keep once the ASTs get big:

```
error: Variable name `unused` is not explicitly referenced.
  Hint: … prefix the name with `_` to silence this warning
```

Nothing external was installed. Lean's linter framework ships in the compiler, and those two
options are the whole configuration — a standalone lint tool would add a dependency and a second
config file to say what these two flags already say. Mathlib's linters (`#lint`,
`#field_linter`, the style family) are genuinely useful, but they require `import Mathlib`, which
is exactly what this library refuses; they arrive with `Spec/` in Part III, where that import is
already paid for.

When a linter is simply wrong, silence it *locally* — `set_option linter.unusedVariables false`
around that one declaration, with a comment saying why. A bare suppression committed without a
reason is how a style gate turns into wallpaper.

One consequence worth knowing before it surprises you: `warningAsError` promotes Lean's own
warnings as well as linter messages, so `sorry` is a build failure in `Sprite/`, not a warning.

```
error: declaration uses `sorry`
```

That enforces standing rule 5 (no silent `sorry`) with the compiler instead of a `grep`, but it
does collide with the book's allowance for a *deliberate*, documented `sorry` in a stretch item.
When you want one, that is the moment to reach for the escape hatch —
`set_option warningAsError false` on the declaration, plus the reason.

## The corpus, before the checker

```sh
mkdir -p test && cp -r /tmp/sprite/test/L{1..8} test/
mkdir -p vendor && cp -r /tmp/sprite vendor/sprite-lang && rm -rf vendor/sprite-lang/.git
echo 'vendor/' >> .gitignore
```

`vendor/sprite-lang` is the reference implementation, kept locally as an oracle you are allowed
to read and never to import. Two chapters in particular (13, 15, 18) are unwinnable without it.

The first program we will ever check is `test/L1/pos/inc00.re`, and it shows the one piece of
surface syntax that needs explaining:

```re
/*@ val inc: x:int => int[v|v = x + 1] */
let inc = (x) => {
    x + 1
};

let bar = inc(10);
```

The annotation is a *C-style comment*. That is a decision with consequences: the tokenizer
cannot skip `/* … */`, because inside it lives a whole little language of types and predicates.
Chapter 5 is where that bill comes due.

## The executable

`lakefile.lean` grows a library and an executable:

```lean
@[default_target]
lean_lib Sprite where
  globs := #[.andSubmodules `Sprite]

@[default_target]
lean_exe sprite where
  root := `Sprite.Main
```

Argument parsing goes in [Sprite/Cli.lean](../Sprite/Cli.lean) as a *pure* function, which is
what makes it testable at all:

```lean
inductive Cmd where
  | version
  | help
  | check (level : Nat) (file : String)
  | usage (msg : String)
  deriving BEq

def parseArgs : List String → Cmd
  | []                    => .usage usageMessage
  | ["--version"]         => .version
  | ["--help"]            => .help
  | ["-h"]                => .help
  | [lvl, file]           =>
      match lvl.toNat? with
      | some 0      => .usage s!"level must be 1..{maxLevel}, got 0"
      | some n      =>
          if n ≤ maxLevel then .check n file else .usage s!"level must be 1..{maxLevel}, got {n}"
      | none        => .usage s!"level must be a number 1..{maxLevel}, got '{lvl}'"
  | _                     => .usage usageMessage

#guard parseArgs ["8", "test/L8/pos/listSet.re"] == .check 8 "test/L8/pos/listSet.re"
#guard parseArgs ["9", "x.re"] == .usage "level must be 1..8, got 9"
```

https://lean-lang.org/doc/reference/latest/Basic-Types/Strings/#String___intercalate

explain	BEq

https://lean-lang.org/doc/reference/latest/Terms/Pattern-Matching/

Nine `#guard`s, all checked by the kernel every time you build, all in the same file as the code.
Note `==` rather than `=`: we would rather write `example : parseArgs … = … := by decide`, but
`deriving DecidableEq` is implemented in the `Lean` library, and importing `Lean` here is exactly
the thirty-second import we just refused. `BEq` is in core. `decide` is not worth the dependency.

[Sprite/Main.lean](../Sprite/Main.lean) turns `Cmd` into output and an exit code:

```lean
def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .version => IO.println s!"sprite {version}"; return 0
  | .help    => IO.println usageMessage; return 0
  | .usage msg => IO.eprintln msg; return exitUsage
  | .check level file =>
      match ← readFile? file with
      | none => IO.eprintln s!"sprite: cannot read '{file}'"; return exitNoInput
      | some contents =>
          IO.println s!"sprite {version}, level {level}: {file}"
          IO.println s!"  {contents.length} bytes"
          IO.eprintln "sprite: no type checker yet — that is Ch 9's job"
          return exitTodo
```

Exit codes follow [sysexits(3)](https://www.freebsd.org/cgi/man.cgi?query=sysexits): 64 for a
bad command line, 66 for an unreadable file. Code 2 is ours and means *"your command line was
fine; my checker does not exist yet"*. Distinguishing "you were wrong" from "I am not finished"
is what lets a test harness treat them differently in Chapter 10.

https://lean-lang.org/doc/reference/latest/Basic-Types/Integers/#Int
On UInt32

 Not a style choice — Lean's entry point accepts exactly (List String →)? IO (UInt32 | Unit | PUnit). IO Int is a type error; I hit that message before switching (UInt8, the type you'd guess since codes are
 one byte, is rejected too).

 Given that, UInt32 is the right shape for three reasons:

 1. It round-trips with child processes. IO.Process.Output.exitCode : UInt32 in core — so when the checker starts shelling out to z3, return r.exitCode just works. A Int-typed main would force a cast at
    exactly the place where you want to propagate a subprocess's code.
 2. It deletes a class of bug. exit -1 and exit 255 are the same observable event:
    ```
      bash -c 'exit -1'  → $? = 255
    ```
    Unsigned makes the negative half unrepresentable.
 3. It's neither a machine word nor oversized. USize would make your exit code's type platform-dependent; UInt64 would be a lie the C ABI (exit(int)) has to truncate anyway.

 Contrast Haskell, where System.Exit gives you ExitFailure Int and the docs tell you to stay in 1..255 — same semantics, Lean just removed the half that can't be observed.

 But UInt32 still doesn't encode the real constraint. POSIX keeps only the low 8 bits:

 ```
   bash -c 'exit 300'  → $? = 44
 ```

 so returning 300 collides silently with returning 44, and nothing in the type stops you. That's why our exit codes are named (exitUsage : UInt32 := 64, exitNoInput := 66, exitTodo := 2) instead of literals
 at call sites, and why the Chapter 10 harness compares exact codes rather than "nonzero". If the codebase ever wants the type to carry the constraint, the honest type is Fin 256, not UInt32 — but main won't
 accept it, so you'd be proving h : n < 256 at the boundary to hand Lean a UInt32 anyway. Not worth it for three constants.


## What the machine said

```
$ lake build
✔ [10/10] Built sprite:exe (869ms)
Build completed successfully (10 jobs).

$ lake exe sprite --version
sprite 0.1.0
exit=0

$ lake exe sprite --help
usage: sprite <level> <file>
       sprite --version | --help
  <level> picks the language: 1 λ, 2 λβ, 3 λκ, 4 λα, 5 λδ, 6 λρ, 7 λτ, 8 λπ
exit=0

$ lake exe sprite 1 test/L1/pos/inc00.re
sprite: no type checker yet — that is Ch 9's job
sprite 0.1.0, level 1: test/L1/pos/inc00.re
  96 bytes
exit=2

$ lake exe sprite 1 test/L1/pos/nope.re
sprite: cannot read 'test/L1/pos/nope.re'
exit=66

$ lake exe sprite 9 test/L1/pos/inc00.re
level must be 1..8, got 9
exit=64
```

Two things in that transcript are not bugs and will not be fixed. The level banner appears
*after* the error because stdout is block-buffered when it is a pipe while stderr is not — when
you start comparing output against golden files in Chapter 10, this ordering will bite you, and
knowing it is a buffering artifact and not a logic error will save you an hour. And the
"96 bytes" for a file that looks shorter than that is a byte count, not a character count: the
`.re` files are ASCII today, and will stop being so the day you write a predicate with `≤` in it.

## Design discussion

**Why a subprocess, when libraries exist.** Three options for talking to a solver: link libz3
through FFI, depend on a Lean-to-SMT library, or write SMT-LIB text and fork `z3 -in -smt2`.
FFI buys speed we do not need at tutorial scale and costs you a build system on two platforms.
Libraries that push *Lean goals* at a solver (`lean-smt`, `Blaster`) have the wrong input type
for us: their currency is `Lean.Expr`, ours is a predicate AST we have not defined yet, and
compiling our AST into `Lean.Expr` to satisfy them means importing `Lean` — the import we just
refused. Forking a process is about forty lines, is what the reference implementation does, and
leaves every later decision (logic, timeouts, unsat cores, model extraction) in our hands.

**Why a surface syntax, when Lean has one.** We could embed sprite in Lean: define the AST as
an `inductive`, write programs with `Expr.let' …`, and get a parser for free. But then we would
be writing tactics over Lean's syntax rather than a checker over sprite's, and we would lose
the 113-file corpus that is our spec. The `.re` syntax is small enough to parse in one chapter
and real enough to be worth keeping.

**Why the level is an argument.** The eight languages are cumulative, so the natural design is
one binary that grows. Passing `1`–`8` explicitly (rather than inferring the richest language a
file can be checked in) keeps failure modes honest: when a level-3 program starts failing, we
want to know that *our* level-3 checker regressed, not that feature detection changed the
question. It also matches the reference implementation's CLI, `sprite 8 test/L8/pos/listSet.re`,
so the two can be run side by side on the same file.

**Why `pos` and `neg` directories rather than annotations.** A test that only asserts
"compiles" cannot tell you that the checker accepted everything. Splitting the corpus by
expected outcome, and giving the checker distinct exit codes for *your* error and *my* error, is
what makes the `neg/` files load-bearing.

## Challenge

**The exit code is a contract (**). Write `test/cli.sh` that runs the executable over every file
in `test/L1` and asserts: exit 2 for a readable file, 66 for a missing one, 64 for a bad level,
0 for `--help` and `--version`. Make it fail loudly, print the offending file, and exit non-zero
so you can run it as a build gate.

Then break it deliberately: pass a directory as the file, pass `--version` *and* a file, pass a
level like `07` or `1x`. Each of those is a case your parser handles by accident. Add the case,
add the `#guard` that pins the behavior, and only then fix `parseArgs`.

*** extension: the interleaving in the transcript above is real. Make `test/cli.sh` compare
stdout and stderr separately, and note in `NOTES.md` which of your assertions would have failed
had you compared them merged.

## Inspiration

- *Refinement Types* §1–§2 — the introduction (the four motivating failures) and the logic of
  Fig. 2.1. Read §2.3 on why the predicates must stay quantifier-free; it is the reason we are
  allowed to trust a solver's answer.
- *Crafting Interpreters* ch. 1–3, for the shape of a chapter and the "start with the whole
  program" posture — note how early Nystrom gets a running binary in front of you.
- The [Blaster README](https://github.com/input-output-hk/Lean-blaster), specifically the
  "NOTE" under *Call to the solver*: an SMT-backed Lean tactic that closes `Valid` goals with an
  `admit`. Useful as an oracle, unusable as a proof — which is precisely why Chapter 26 ends with
  an axiom audit.

## Notes for `NOTES.md` (the four errors this chapter actually produced)

1. `executable sprite where …` — not a Lake keyword; it is `lean_exe`.
2. `System.argv` and `IO.argv` do not exist in core 4.35. Arguments arrive as a parameter:
   Lean accepts exactly `(List String →)? IO (UInt32 | Unit)` for `main`. `UInt8` is rejected.
3. `main` inside `namespace Sprite` is `Sprite.main`, which is not an entry point — and Lake
   still builds an executable, which then runs someone else's `main` and panics with
   `import failed, trying to import module with anonymous name`. Put `main` in the root namespace.
4. `deriving (BEq, Repr, DecidableEq)` does not parse, and `DecidableEq`/`Repr` are not
   derivable without `import Lean`. Take what core gives you: `deriving BEq`, compare with `==`.

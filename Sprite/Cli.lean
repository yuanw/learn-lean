/-!
Command line argument parsing for the `sprite` executable.

The parser is a pure function `List String → Cmd`, which is why the CLI has anything
testable in it at all: the branches are checked by `decide` here, rather than by running
the executable from the build.
-/

namespace Sprite

/-- The eight language levels of the paper, §3–§10. Level `n` is checked by the checker
    built in Ch 3+3n of `book/`. -/
def maxLevel : Nat := 8

inductive Cmd where
  | version
  | help
  | check (level : Nat) (file : String)
  | usage (msg : String)
  deriving BEq

def usageMessage : String :=
  String.intercalate "\n"
    [ "usage: sprite <level> <file>"
    , "       sprite --version | --help"
    , "  <level> picks the language: 1 λ, 2 λβ, 3 λκ, 4 λα, 5 λδ, 6 λρ, 7 λτ, 8 λπ" ]

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

-- The parser is where the CLI's only logic lives, so it gets tested here rather than by
-- running the executable, which would fork a process during `lake build`.
-- (`deriving DecidableEq` lives in the `Lean` library, so these compare with `==`/BEq.)
#guard parseArgs ["--version"] == .version
#guard parseArgs ["-h"] == .help
#guard parseArgs ["--help"] == .help
#guard parseArgs ["8", "test/L8/pos/listSet.re"] == .check 8 "test/L8/pos/listSet.re"
#guard parseArgs ["0", "x.re"] == .usage "level must be 1..8, got 0"
#guard parseArgs ["9", "x.re"] == .usage "level must be 1..8, got 9"
#guard parseArgs ["x", "y.re"] == .usage "level must be a number 1..8, got 'x'"
#guard parseArgs ["1"] == .usage usageMessage
#guard parseArgs ["1", "a", "b"] == .usage usageMessage
#guard parseArgs [] == .usage usageMessage

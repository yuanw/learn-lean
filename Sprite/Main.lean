import Sprite.Cli
/-!
The `sprite` command line entry point.

    lake exe sprite <level> <file>

Exit codes follow sysexits(3): 64 for a bad command line, 66 for an unreadable input file.
Code 2 means "the command line was fine and the checker does not exist yet", which is the
only honest answer available before Ch 9.

`main` must live in the root namespace -- a `Sprite.main` is not an entry point, and Lake
will happily build an executable that runs someone else's `main` when you get this wrong.
-/

open Sprite

/-- Bumped by hand; `sprite --version` prints it. -/
def version : String := "0.1.0"

/-- sysexits(3) `EX_USAGE`: the command line itself was wrong. -/
def exitUsage : UInt32 := 64
/-- sysexits(3) `EX_NOINPUT`: the command line was fine, the file is not there. -/
def exitNoInput : UInt32 := 66
/-- Ours: command line fine, file readable, checker not written yet. -/
def exitTodo : UInt32 := 2

/-- A missing or unreadable file becomes `none` instead of escaping as an exception, so the
    process can still exit with a meaningful code. -/
def readFile? (file : String) : IO (Option String) := do
  try return some (← IO.FS.readFile file) catch _ => return none

/-- Lean 4.35 accepts exactly these entry-point types: `(List String →)? IO (UInt32 | Unit)`.
    There is no `System.argv` in core, so the arguments arrive as a parameter and the exit
    code goes out as the return value. -/
def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .version =>
      IO.println s!"sprite {version}"
      return 0
  | .help =>
      IO.println usageMessage
      return 0
  | .usage msg =>
      IO.eprintln msg
      return exitUsage
  | .check level file =>
      match ← readFile? file with
      | none =>
          IO.eprintln s!"sprite: cannot read '{file}'"
          return exitNoInput
      | some contents =>
          IO.println s!"sprite {version}, level {level}: {file}"
          IO.println s!"  {contents.length} bytes"
          IO.eprintln "sprite: no type checker yet — that is Ch 9's job"
          return exitTodo

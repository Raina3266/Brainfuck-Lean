import Brainfuck
import Lean.Data.Json

/-!
  # The differential-testing oracle

  A line-oriented JSON protocol over stdin/stdout, so one process can serve
  many queries (spawning a process per query would dominate fuzzing time):

  - request (one per line):
    `{"program": "<brainfuck source>", "input": [n, ...], "fuel": n}`,
    plus an optional `"trace": false` to skip the trace (traces of long runs
    are enormous; timing-only queries don't want them)
  - response (one minified line each):
    - `{"status": "parseError"}` for unbalanced brackets
    - `{"status": "fuel", "nanos": n}` when the budget ran out
    - `{"status": "ok", "nanos": n, "state": {...}, "trace": [...]}` on
      completion; `state` is the terminal state, and `trace` (whose final
      entry repeats the terminal state) is omitted when the request said
      `"trace": false`
    - `{"status": "badRequest", "error": "..."}` for malformed lines (and
      for one "impossible" internal error: `Program.run` succeeding while
      `Program.runTrace` runs out of fuel, which `Fragment.runStackTrace_fst`
      rules out)

  `nanos` is measured here, around the bare interpreter call, so it excludes
  JSON parsing and serialization (and the trace re-run, which is untimed
  instrumentation).

  The timed interpreter is `Program.run`, the one proven equivalent to the
  big-step semantics (`Program.run_iff_execution`), and `Program.runTrace`
  is pinned to it by `Fragment.runStackTrace_fst` — so any disagreement with
  another implementation is a disagreement with `Program.Execution` itself.
-/

open Lean (Json ToJson FromJson toJson fromJson?)
open Brainfuck

structure Request where
  program : String
  input : List Nat
  fuel : Nat
  trace : Option Bool
  deriving Lean.FromJson

def respond (req : Request) : IO Json := do
  match Program.parse req.program with
  | none => return Json.mkObj [("status", "parseError")]
  | some p =>
    let input : List Cell := req.input.map UInt64.ofNat
    let s0 := State.initial input
    let start <- IO.monoNanosNow
    let result <- IO.lazyPure (fun _ => p.run req.fuel s0)
    let stop <- IO.monoNanosNow
    let nanos := toJson (stop - start)
    match result with
    | none => return Json.mkObj [("status", "fuel"), ("nanos", nanos)]
    | some s =>
      /-
        The final state is always reported; the (potentially enormous) trace
        only when requested. Serializing a ~10^6-entry trace costs minutes,
        so clients cap the fuel above which they stop asking for one.
      -/
      let base :=
        [ ("status", Json.str "ok")
        , ("nanos", nanos)
        , ("state", toJson s) ]
      if req.trace = some false then
        return Json.mkObj base
      else
        match p.runTrace req.fuel s0 with
        | none =>
          return Json.mkObj
            [ ("status", "badRequest")
            , ("error", "impossible: run succeeded but runTrace ran out of fuel") ]
        | some trace =>
          return Json.mkObj (base ++ [("trace", toJson trace)])

def handle (line : String) : IO Json := do
  match Json.parse line >>= fromJson? (α := Request) with
  | .error e => return Json.mkObj [("status", "badRequest"), ("error", e)]
  | .ok req => respond req

partial def serve (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line <- stdin.getLine
  if line.isEmpty then
    return
  let trimmed := line.trimAscii
  if trimmed.isEmpty then
    serve stdin stdout
  else
    stdout.putStrLn (<- handle trimmed.toString).compress
    stdout.flush
    serve stdin stdout

def main : IO Unit := do
  serve (<- IO.getStdin) (<- IO.getStdout)

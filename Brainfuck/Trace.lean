import Brainfuck.Interpreter
import Lean.Data.Json

namespace Brainfuck

  /-!
    # Execution traces

    A trace records every state an interpreter passes through, for
    differential testing against other implementations: comparing whole
    traces catches disagreements that identical final states would hide.

    A trace entry is a `State` together with the instruction that was just
    executed (`none` for the initial state). Fuel is deliberately absent:
    both interpreters (`Fragment.runStackTrace` here, and the Rust one in
    `rust/src/interpreter.rs`) charge exactly one fuel unit per recorded
    entry, so the trace length already conveys it.
  -/

  /--
    A concrete instruction, as an interpreter dispatches them: the six
    primitives plus the loop brackets.

    In a trace only `atom` and `beginLoop` ever appear: a loop-guard check
    is a `beginLoop` event (recorded on every check, including re-checks
    after a body and the final one that exits the loop), while `]` is an
    unconditional back-jump that neither interpreter charges or records.
    `endLoop` is still a constructor so that this type (and its JSON
    encoding) covers the full instruction alphabet the Rust side defines.
  -/
  inductive Instruction where
    | atom (a : Atom)
    | beginLoop
    | endLoop

  instance : Lean.ToJson Instruction where
    toJson
      | .atom .inc    => .str "+"
      | .atom .dec    => .str "-"
      | .atom .left   => .str "<"
      | .atom .right  => .str ">"
      | .atom .input  => .str ","
      | .atom .output => .str "."
      | .beginLoop    => .str "["
      | .endLoop      => .str "]"

  deriving instance Lean.ToJson for State

  /--
    One trace entry: the instruction that was just charged (`none` for the
    initial state), and the state after it (for a `beginLoop` guard check,
    the unchanged state at the check).
  -/
  structure TraceEntry where
    instruction : Option Instruction
    state       : State

  instance : Lean.ToJson TraceEntry where
    toJson e :=
      Lean.Json.mkObj
        [ ("instruction", Lean.toJson e.instruction)
        , ("state",       Lean.toJson e.state) ]

  /-- All states an execution passed through, oldest first. -/
  structure ExecutionTrace where
    entries : Array TraceEntry

  /-- Serialized as a bare array: the wrapper struct adds no information. -/
  instance : Lean.ToJson ExecutionTrace where
    toJson t := Lean.toJson t.entries

  namespace Fragment

    /--
      The traced twin of `Fragment.runStack`: same machine, same exact fuel
      meter (one unit per atom and per loop-guard check), but every charged
      instruction pushes a trace entry. `Fragment.runStackTrace_fst` pins
      the two together.
    -/
    def runStackTrace :
        Nat -> List Fragment -> List Frame -> State -> Array TraceEntry ->
          Option (State × Array TraceEntry)
      | _, [], [], s, acc => some (s, acc)
      | 0, [], _ :: _, _, _ => none
      | fuel + 1, [], (body, rest) :: frames, s, acc =>
        let acc := acc.push ⟨some .beginLoop, s⟩
        if s.tape.current = 0 then
          runStackTrace fuel rest frames s acc
        else
          runStackTrace fuel body.inner ((body, rest) :: frames) s acc
      | 0, _ :: _, _, _, _ => none
      | fuel + 1, .atom a :: code, frames, s, acc =>
        let s' := a.apply s
        runStackTrace fuel code frames s' (acc.push ⟨some (.atom a), s'⟩)
      | fuel + 1, .loop body :: code, frames, s, acc =>
        let acc := acc.push ⟨some .beginLoop, s⟩
        if s.tape.current = 0 then
          runStackTrace fuel code frames s acc
        else
          runStackTrace fuel body.inner ((body, code) :: frames) s acc

    /--
      The traced interpreter agrees with the proven one: same fuel, same
      verdict, same final state — the trace is pure instrumentation.
    -/
    theorem runStackTrace_fst :
        ∀ {fuel : Nat} {code : List Fragment} {frames : List Frame} {s : State}
          {acc : Array TraceEntry},
          (runStackTrace fuel code frames s acc).map Prod.fst = runStack fuel code frames s := by
      intro fuel
      induction fuel with
      | zero =>
        intro code frames s acc
        cases code with
        | nil =>
          cases frames with
          | nil         => simp [runStackTrace, runStack]
          | cons fr frs => simp [runStackTrace, runStack]
        | cons f rest => simp [runStackTrace, runStack]
      | succ n ih =>
        intro code frames s acc
        cases code with
        | nil =>
          cases frames with
          | nil => simp [runStackTrace, runStack]
          | cons fr frs =>
            obtain ⟨body, rest⟩ := fr
            simp only [runStackTrace, runStack]
            by_cases hz : s.tape.current = 0
            · rw [if_pos hz, if_pos hz]
              exact ih
            · rw [if_neg hz, if_neg hz]
              exact ih
        | cons f rest =>
          cases f with
          | atom a => simpa [runStackTrace, runStack] using ih
          | loop body =>
            simp only [runStackTrace, runStack]
            by_cases hz : s.tape.current = 0
            · rw [if_pos hz, if_pos hz]
              exact ih
            · rw [if_neg hz, if_neg hz]
              exact ih

  end Fragment

  namespace Program

    /--
      Run a program, recording the full trace. Fuel semantics are exactly
      those of `Program.run` (`Fragment.runStackTrace_fst`): `none` iff
      `Program.run` gives `none`.
    -/
    def runTrace (p : Program) (fuel : Nat) (s : State) : Option ExecutionTrace :=
      match Fragment.runStackTrace fuel p.inner [] s #[⟨none, s⟩] with
      | none              => none
      | some (_, entries) => some ⟨entries⟩

    theorem runTrace_isSome_iff_run {p : Program} {fuel : Nat} {s : State} :
        (p.runTrace fuel s).isSome ↔ (p.run fuel s).isSome := by
      have h := Fragment.runStackTrace_fst
        (fuel := fuel) (code := p.inner) (frames := []) (s := s) (acc := #[⟨none, s⟩])
      rw [runTrace, run]
      cases hb : Fragment.runStackTrace fuel p.inner [] s #[⟨none, s⟩] with
      | none =>
        rw [hb] at h
        simp only [Option.map_none] at h
        simp [← h]
      | some pair =>
        rw [hb] at h
        simp only [Option.map_some] at h
        simp [← h]

  end Program

  /- one increment: the initial state plus one `+` entry -/
  example :
      ((bf! { + }).runTrace 1 (State.initial [])).map
        (fun t => t.entries.toList.map (fun e => e.state.tape.current)) =
      some [0, 1] := by
    rfl

  /- the guard of a skipped loop is still an event -/
  example :
      ((bf! { [ + ] }).runTrace 1 (State.initial [])).map
        (fun t => t.entries.size) =
      some 2 := by
    rfl

  /-
    `, [ - ] .` on input 1, exact budget: `,` then guard, `-`, the exiting
    guard re-check (the back-jump is fused into it), `.` — five events, six
    entries.
  -/
  example :
      ((bf! { , [ - ] . }).runTrace 5 (State.initial [1])).map
        (fun t => t.entries.size) =
      some 6 := by
    rfl

end Brainfuck

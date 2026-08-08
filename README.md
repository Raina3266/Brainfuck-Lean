This project contains the following:
- A semantics for Brainfuck written in Lean, as well as formalizations of two
  example programs (modular addition and a trivial infinite loop) with
  corresponding correctness proofs.
- A parser for Brainfuck in Lean, and a corresponding Lean macro
- A Brainfuck interpreter, written in Lean, proven against the semantics
- A Brainfuck interpreter, written in Rust, fuzzed against the Lean interpreter
- A Rust program to produce a standalone Lake project containing a term
  `program : Program` which represents an input Brainfuck program.
- Test coverage

## Usage 

First, install the Rust program. From the project root:
```sh
cargo install --path rust
brainfuck --help  # check if installed properly
```

From there, to produce a Lake project for a specific Brainfuck program, run:
```sh
brainfuck lower \
  --source path/to/brainfuck.bf \
  --project-name my-brainfuck-project \
  --output-path ..
```

This will produce a Lake project at `../my-brainfuck-project`, which will
contain a `MyBrainfuckProject.lean` file containing `def program : Program :=
embed_bf! "..."`. You can then analyze `program` using lemmas provided by the
`Brainfuck` Lean library (this project).

> Note: The Rust code does not validate the Brainfuck code in any way. It
> naively copies it to the output Lake project. If the Brainfuck is invalid
> (i.e. unmatched brackets), the Rust code may produce warnings, but will still
> produce the Lake project. The `embed_bf!` macro, however, will cause a compile
> error in this case. To see the errors, run `brainfuck analyze
> path/to/brainfuck.bf`.

Alternatively, to execute a Brainfuck program using the Rust interpreter, run:
```sh
brainfuck run \
  --source path/to/brainfuck.bf \
  --input "1 2 3"
```
`--input` accepts a single string, which is interpreted as a list of 64-bit
unsigned integers, separated by a single "space" character. Any other format is
an error.

To execute Brainfuck using the Lean interpreter, use `#eval program.interpret
input fuel` in a Lean file.

## Specification

In the assignment, some parts of the language were left unspecified. Here are
the choices made:
- Each cell is represented by a 64-bit unsigned integer, so the maximum value
  is `max := (2^64) - 1`
- Arithmetic is wrapping, so:
  - if the value of the current cell is `max`, then an increment instruction
    will leave it as `0`
  - if the value of the current cell is `0`, then a decrement instruction will
    leave it as `max`
- The tape is bi-infinite
- The tape begins initialized to zero in all cells
- When reading input, if there is no input left, the current cell will be set
  to `0`

These choices were made because they make the implementation simpler. In
particular, if a program successfully parses, then it will not encounter runtime
errors (ignoring fuel).

In a production environment, I might consider alternatives, depending on the
system I am modelling. For example, reading from empty input may either be
interpreted as:
- a bug
- an idiomatic way to quickly set a cell to zero

If it was known that reading from an empty input was *always* a bug, I would
perhaps model that error case separately, so that proofs can show that a program
never does this.

## Core data structures

- `Tape` - the bi-infinite memory tape. Implemented as a `Quotient RawTape`
- `State` - a triple containing a tape, the remaining inputs that have not been
  read yet, and the outputs that have been produced so far
- `Atom` - an atomic instruction: increment, decrement, move left, move right,
  read input, print output (but not begin/end loop).
- `Program` and `Fragment` - mutually-recursive types representing a parsed
  program. These types are incapable of representing programs with unmatched
  brackets, and therefore always represent valid programs.
  - `Program.parse (brainfuck : String) : Option Program` parses a program,
    returning `.none` in the unbalanced-bracket case
- `Transition` - a state transition caused by an `Atom`. It contains an `Atom`,
  and both `old` and `new` `State`s. Notably, since it refers to state
  transitions caused by `Atom`s, it does not model loops at all.

## Semantics

The semantics is split into two parts:
- Local semantics for atomic instructions (increment, decrement, move
  left/right, input, output)
- Big-step semantics for whole programs, including loops

`Transition.IsValid` is an inductive `Prop` that enumerates all possible valid
state transitions that can be caused by an atomic instruction. This forms the
local semantics.

The big-step semantics is structurally similar to the local semantics. There is
a `Program.Execution` relation (a thin wrapper around the inductive `Prop`
`Fragment.ExecutionList`), which is parameterized over an initial `State` and a
terminal `State`. In other words, `myProgram.Execution stateI
stateT` is a `Prop` which means "when you run `myProgram` from initial state
`stateI`, it terminates, and the final state is `stateT`".

We also define two notations:
- `s0 >-[atom]-> s1` is syntax sugar for `Transition.IsValid { atom := atom,
  old := s0, new := s1 }`
- `si ==[prog]=> st` is syntax sugar for `Program.Execution prog si st`

The big-step semantics uses the local semantics' definition of validity for
atomic instructions, with extra constructors for handling loops, as well as a
trivial empty-program case.

This allows us to express statements about (non-)termination. In
`Execution.lean`, we have:
```lean
namespace Program

  def Halts (p : Program) (s : State) : Prop :=
    ∃ s', s ==[p]=> s'

  def Diverges (p : Program) (s : State) : Prop :=
    ¬ p.Halts s

end Program
```
While the Halting Problem is undecidable in the general case (i.e. for all
programs and all inputs), it is not always undecidable in the case of specific
programs. In `Brainfuck.Examples`, we prove both that a program halts, and that
another program diverges.

### Example 1: Modular Addition

In `Brainfuck.Examples.Add`, we have:
```lean
def program : Program := embed_bf! "corpus/add.bf"  -- , > , [ - < + > ] < .

def addSpec : Program.Spec
  | [x, y] => .some [x + y]
  | _      => .none

-- ...

theorem add_correct : program.Computes addSpec := by -- ...
```
Unfolding `Program.Computes`, this proves the following:
- for any two input values `x` and `y`, running the add program from an initial
  state with those two cells as inputs **will eventually terminate** with some
  final state `stateT`
- `stateT.output` contains a single value, which is equal to the wrapping sum
  `x + y`
- `stateT.input` is empty
- for inputs of any other shape, `addSpec` is `.none`, so the theorem makes no
  claim at all

Note that this theorem makes no claims about this program when started from
non-initial states (an initial state has an all-zero tape, the given input,
and no output yet).

We separately prove that, for *any state*, the addition program terminates in
`theorem add_halts (state : State) : program.Halts state`. However, this
proof makes no claims about the output in this case.

### Example 2: Infinite Loop

We also prove non-termination of a simple infinite loop in
`Brainfuck.Examples.InfiniteLoop`:

```lean
  -- `+ [ ]` loops forever from any *initial* state, but halts when the
  -- current cell starts at `2^64 - 1` (the `+` wraps it to zero); this
  -- stronger variant clears the cell first, so it diverges from *every* state
  private def strongerProgram : Program := bf! { [ - ] + [ ] }

  -- ...

  theorem strongerProgram_diverges_everywhere (s : State) 
      : strongerProgram.Diverges s := by
    -- ...
```
Here we have shown that, for any state `s`, there exists no `stateT` for which
`s ==[strongerProgram]=> stateT`, and therefore it never terminates,
regardless of initial state.

## Trust

By implementing the full pipeline (parser, semantics and verified interpreter)
in Lean, there are relatively few unverified (trusted) parts of the execution:
- the Lean kernel itself
- the parsing logic, while implemented in Lean, is not fully verified. For
  example, there is no "proof" that the parser does not mix up the `+` and `-`
  symbols. However, there are tests and proofs that would fail if this were the
  case. But these tests do not fully cover every possible error.
  - Note that the `bf!` macro is intended as syntax sugar, and fails in some
    simple cases (e.g. Lean interprets `--` as a comment). `embed_bf!
    "path/to/brainfuck.bf"` is intended as the definitive way to produce a term
    of type `Program` from a file containing a Brainfuck string
  - The `parse` function also has several proofs of correctness, but they do not
    form a full specification. Rather, these act like "exhaustive property
    tests". Reassuring for correctness, but does not guarantee bug-freedom.

## Interpreter

This project contains two interpreter implementations:
- A Lean implementation, which executes a `Program` and is proven against the
  semantics of `Program.Execution`
- A Rust implementation, which executes a Brainfuck string, and is not proven
  at all 

The Rust implementation, while not proven, has certain advantages:
- It is significantly faster (5-10x approximately)
- It uses less memory
- It does not require a `fuel` parameter (unlike the Lean interpreter, it need
  not be a provably-total function), so infinite loops are supported.
  - If this is undesirable, a `fuel` parameter can optionally be provided to
    force termination.
- being written in Rust, which has essentially no runtime, it is much easier to
  compile to a shared library and embed in other languages (e.g. Python, Java,
  etc.)

However, it is not verified. While a tool like Aeneas could be used to bridge
the gap between the Rust interpreter code and a Lean proof that it has the same
behaviour as the Lean interpreter, I did not set this up. Instead, I used
differential fuzzing to:
- Generate random programs and random inputs (and a random fuel)
- Execute both interpreters against the same inputs
- Assert that both interpreters agree on the outcome: the same final state, or
  running out of fuel together (both meter fuel identically), or both rejecting
  the program
- For runs short enough that the trace stays manageable, additionally produce
  an `ExecutionTrace` from each interpreter and assert that they are identical
  - An `ExecutionTrace` records, for each state the interpreter passes through,
    the instruction that was just executed and the resulting `state` (fuel is
    deliberately omitted: both interpreters charge one unit per entry, so the
    trace length already conveys it)

While not a "proof", it is a stronger approach than simply "testing a fixed set
of cases". This fuzzing job can be left running indefinitely, searching for
deviations. The fuzzing harness is also relatively sophisticated, and is able
to use special instructions emitted by LLVM to inspect code-coverage of the
Rust code, and as such is able to explore more thoroughly, by analyzing which
machine-code-level branches have been taken.

In fact, a very similar design is used by [Cedar][cedar], a policy language
developed by AWS used for defining access control rules. They have a Rust
implementation, as well as a verified Lean implementation, and use differential
fuzzing to assert that they give the same answer in all tested cases.

## Time split

The majority of the time was actually spent learning Lean. Before this
assignment, I have never written Lean, or any functional programming language in
fact!

This covered basics of functional programming (immutable data, recursion over
iteration, currying, etc.), as well as the logic/theory behind Lean
(Curry-Howard Correspondence/"propositions-as-types", dependent type theory). I
also spent some time learning some basic theorem proving, getting used to
tactic mode, and using some basic tactics.

For the actual assignment, I spent a few hours per day on it:
- day 1: basic types: `Tape`, `State`, `Program` (and `parse`), etc.
  - for much of this, I was still getting familiar with general programming in
    Lean
- day 2: `Transition` and `Transition.IsValid`, and some simple proofs
  of (in)validitiy of trivial transitions, as well as proofs about the parser.
- day 3-4: `Program.Execution` as well as trivial proofs. Also added `bf!` macro
  and related.
- day 5: `Examples` and most of the Rust code (I spent longer today, since the
  Rust code is a lot less mentally-tiring since I'm very familiar with it, so it
  felt quite relaxing).
- day 6: The Lean interpreter and proofs against Lean semantics
- day 7: Setting up fuzzing and cleanup

### AI Usage

I used AI heavily for this project. In particular, I used two different
agents/models:
- For overall design work, as well as exploratory learning of new concepts (FP
  basics, Curry-Howard, dependent types, etc.), I used Kimi K3 with the
  Zed agent
- For the majority of the actual proofs, I used Leanstral via the Mistral Vibe
  TUI

I understand the structure of the code well, but I couldn't explain most of the
actual tactic-mode proofs. However, I am satisfied that I understand the type
signatures - i.e. I understand *what the proof is claiming*. From there, I trust
Lean that, since it compiles, the proof must be valid. I suspect there are
possible improvements in readability/performance of the proofs, but I am not
able to analyze that.



[Cedar]: https://www.cedarpolicy.com/



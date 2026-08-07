## Coding style

Each of the following sections applies only to the specific language, and should be entirely disregarded when writing a different language.

### Lean

Generally, one type per file, unless a type is completely trivial.

When checking that something builds, make sure that `lake build` would actually import the file in question. Errors in non-exported files are not reported. Using LSP diagnostics may be more reliable in this case.

Aim to keep lines shorter than 100 chars wide, but it is acceptable to overflow this in extreme cases. Where possible, try to format code such that "equivalent syntax" is in the same column, for example:
```lean
-- good
match foo with 
| .none     => "nothing"
| .some 1   => "no number"
| .some 123 => "big number"

-- bad
match foo with 
| .none => "nothing"
| .some 1 => "no number"
| .some 123 => "big number"
```

Block comment markers (all styles, `/--`, `/-!`, and `/-`) should be on their own lines (unless the comment itself is single line):
```lean
-- good
/-
  A block comment
  that is multiple lines
-/

-- bad
/- A block comment
  that is multiple lines -/

-- good
/- A single line block comment -/

-- bad
/- 
  A single line block comment 
-/
```

Avoid using "method call syntax" for constructors:
```lean
-- good
def x : Nat := .succ 0

-- bad
def x : Nat := 0.succ
```
This applies to both actual constructors, as well as "constructor-like
functions" (i.e. functions that take some input and wrap them in a larger
structure).

Prefer unicode symbols in "proof-like parts" and ascii in "programming-like parts". 

Indent content inside a `namespace`.

Prefer using `by` even for very simple proofs rather than lambdas or other term-mode techniques. Only for *absolutely trivial* proofs should you use term-mode.

Don't use `:= ` to define instances:
```lean
-- bad
instance : Inhabited Foo where
  default := new

-- bad
instance : Inhabited Foo := ⟨ new ⟩
```


### Rust

Avoid comments, unless:
- they are `SAFETY` comments
- explicitly told to add comments by the user

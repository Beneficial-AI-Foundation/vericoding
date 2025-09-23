-- <vc-preamble>
@[reducible, simp]
def only_once_precond (a : Array Int) (key : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
def only_once_loop {T : Type} [DecidableEq T] (a : Array T) (key : T) (i keyCount : Nat) : Bool :=
  if i < a.size then
    match a[i]? with
    | some val =>
        let newCount := if val = key then keyCount + 1 else keyCount
        only_once_loop a key (i + 1) newCount
    | none => keyCount == 1
  else
    keyCount == 1
-- </vc-helpers>

-- <vc-definitions>
def only_once (a : Array Int) (key : Int) (h_precond : only_once_precond (a) (key)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def count_occurrences {T : Type} [DecidableEq T] (a : Array T) (key : T) : Nat :=
  a.foldl (fun cnt x => if x = key then cnt + 1 else cnt) 0
@[reducible, simp]
def only_once_postcond (a : Array Int) (key : Int) (result: Bool) (h_precond : only_once_precond (a) (key)) :=
  ((count_occurrences a key = 1) → result) ∧
  ((count_occurrences a key ≠ 1) → ¬ result)

theorem only_once_spec_satisfied (a: Array Int) (key: Int) (h_precond : only_once_precond (a) (key)) :
    only_once_postcond (a) (key) (only_once (a) (key) h_precond) h_precond := by
  sorry
-- </vc-theorems>
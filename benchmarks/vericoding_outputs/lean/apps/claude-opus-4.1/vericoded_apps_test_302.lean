import Mathlib
-- <vc-preamble>
def pow (base exp : Nat) : Nat :=
  if exp = 0 then 1 else base * pow base (exp - 1)

def repunit (n : Nat) : Nat :=
  if n = 0 then 0 
  else if n = 1 then 1
  else if n = 2 then 11
  else if n = 3 then 111
  else if n = 4 then 1111
  else if n = 5 then 11111
  else n

def ValidInput (n : Nat) : Prop := True

def ValidOutput (n result : Nat) : Prop :=
  (n = 0 → result = 0) ∧ (n > 0 → result > 0)

@[reducible, simp]
def solve_precond (n : Nat) : Prop := ValidInput n
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma repunit_positive (n : Nat) (h : n > 0) : repunit n > 0 := by
  unfold repunit
  split
  · next h_eq =>
    rw [h_eq] at h
    exact absurd h (Nat.not_lt_zero 0)
  · split
    · norm_num
    · split
      · norm_num
      · split
        · norm_num
        · split
          · norm_num
          · split
            · norm_num
            · exact h
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Nat) (h_precond : solve_precond n) : Nat := repunit n
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n result : Nat) (h_precond : solve_precond n) : Prop :=
  ValidOutput n result

theorem solve_spec_satisfied (n : Nat) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  unfold solve_postcond ValidOutput solve
  constructor
  · intro h_eq
    simp [h_eq, repunit]
  · intro h_pos
    exact repunit_positive n h_pos
-- </vc-theorems>

import Mathlib
-- <vc-preamble>
partial def count_sf_flights (s : String) : Int :=
  if s.length ≤ 1 then 0
  else (if s.get ⟨s.length - 1⟩ = 'F' ∧ s.get ⟨s.length - 2⟩ ≠ 'F' then 1 else 0) + count_sf_flights (s.take (s.length - 1))

partial def count_fs_flights (s : String) : Int :=
  if s.length ≤ 1 then 0
  else (if s.get ⟨s.length - 1⟩ = 'S' ∧ s.get ⟨s.length - 2⟩ ≠ 'S' then 1 else 0) + count_fs_flights (s.take (s.length - 1))

@[reducible, simp]
def solve_precond (n : Int) (s : String) : Prop :=
  n ≥ 2 ∧ s.length = n ∧ ∀ i, 0 ≤ i ∧ i < s.length → s.get ⟨i⟩ = 'S' ∨ s.get ⟨i⟩ = 'F'
-- </vc-preamble>

-- <vc-helpers>

-- LLM HELPER
/-- The condition for the string to result in a "YES". -/
def is_yes (s : String) : Prop := count_sf_flights s > count_fs_flights s

-- LLM HELPER
/-- The `is_yes` proposition is decidable. -/
instance (s : String) : Decidable (is_yes s) := by
  unfold is_yes
  infer_instance

-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (s : String) (h_precond : solve_precond n s) : String :=
  if is_yes s then "YES" else "NO"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (s : String) (result : String) (h_precond : solve_precond n s) : Prop :=
  (result = "YES" ∨ result = "NO") ∧ (result = "YES" ↔ count_sf_flights s > count_fs_flights s)

theorem solve_spec_satisfied (n : Int) (s : String) (h_precond : solve_precond n s) :
    solve_postcond n s (solve n s h_precond) h_precond := by
  unfold solve solve_postcond is_yes
  split_ifs <;> simp [*]
-- </vc-theorems>

-- <vc-preamble>
-- <vc-preamble>
def IsStrongestInSchool (student_idx: Nat) (powers: List Int) (schools: List Int) : Prop :=
  student_idx < powers.length ∧ powers.length = schools.length ∧
  ∀ j, j < powers.length ∧ schools[j]! = schools[student_idx]! → powers[j]! ≤ powers[student_idx]!

instance (student_idx: Nat) (powers: List Int) (schools: List Int) : Decidable (IsStrongestInSchool student_idx powers schools) :=
  sorry

@[reducible, simp]
def solve_precond (n m k : Int) (powers schools chosen : List Int) : Prop :=
  n ≥ 1 ∧ m ≥ 1 ∧ k ≥ 1 ∧ k ≤ n ∧ m ≤ n ∧
  powers.length = n.natAbs ∧ schools.length = n.natAbs ∧ chosen.length = k.natAbs ∧
  (∀ i, i < n.natAbs → 1 ≤ schools[i]! ∧ schools[i]! ≤ m) ∧
  (∀ i, i < k.natAbs → 1 ≤ chosen[i]! ∧ chosen[i]! ≤ n) ∧
  (∀ i j, i < k.natAbs ∧ j < k.natAbs ∧ i ≠ j → chosen[i]! ≠ chosen[j]!) ∧
  (∀ i j, i < n.natAbs ∧ j < n.natAbs ∧ i ≠ j → powers[i]! ≠ powers[j]!) ∧
  (∀ s, 1 ≤ s ∧ s ≤ m → ∃ i, i < n.natAbs ∧ schools[i]! = s) ∧
  (∀ i, i < n.natAbs → 1 ≤ powers[i]! ∧ powers[i]! ≤ n)
-- </vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- <vc-definitions>
def solve (n m k : Int) (powers schools chosen : List Int) (h_precond : solve_precond n m k powers schools chosen) : Int :=
  sorry
-- </vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m k : Int) (powers schools chosen : List Int) (result: Int) (h_precond : solve_precond n m k powers schools chosen) : Prop :=
  result ≥ 0 ∧ result ≤ k ∧
  result = Int.ofNat ((List.range k.natAbs).filter (fun i => !IsStrongestInSchool (chosen[i]!.natAbs - 1) powers schools) |>.length)

theorem solve_spec_satisfied (n m k : Int) (powers schools chosen : List Int) (h_precond : solve_precond n m k powers schools chosen) :
    solve_postcond n m k powers schools chosen (solve n m k powers schools chosen h_precond) h_precond := by
  sorry
-- </vc-theorems>
-- </vc-theorems>

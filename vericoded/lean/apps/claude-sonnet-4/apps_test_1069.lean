import Mathlib
-- <vc-preamble>
def StringToNat (s : String) : Nat :=
  s.toList.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

def ValidInput (n : String) : Prop :=
  n.length > 0 ∧ 
  (∀ i, i < n.length → '0' ≤ n.data[i]! ∧ n.data[i]! ≤ '9') ∧
  (n.data[0]! ≠ '0' ∨ n.length = 1)

def ValidOutput (result : String) : Prop :=
  result = "4\n" ∨ result = "0\n"

@[reducible, simp]
def solve_precond (n : String) : Prop :=
  ValidInput n
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Check if a natural number is divisible by 4
def isDivisibleBy4 (n : Nat) : Bool :=
  n % 4 = 0

-- LLM HELPER: Helper lemma about modular arithmetic
lemma mod_four_cases (n : Nat) : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
  have h := Nat.mod_lt n (by norm_num : (0 : Nat) < 4)
  interval_cases (n % 4) <;> simp

-- LLM HELPER: StringToNat preserves divisibility properties we need
lemma stringToNat_mod_four (s : String) (h : ValidInput s) :
  (StringToNat s % 4 = 0) ∨ (StringToNat s % 4 ≠ 0) := by
  cases' mod_four_cases (StringToNat s) with h1 h2
  · left; exact h1
  · right; cases' h2 with h2 h3
    · norm_num [h2]
    · cases' h3 with h3 h4
      · norm_num [h3]
      · norm_num [h4]

-- LLM HELPER: Convert between decidability and propositions
lemma decide_iff_prop (p : Prop) [Decidable p] : decide p = true ↔ p := by
  simp [decide_eq_true_iff]
-- </vc-helpers>

-- <vc-definitions>
def solve (n : String) (h_precond : solve_precond n) : String :=
  if StringToNat n % 4 = 0 then "4\n" else "0\n"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : String) (result : String) (h_precond : solve_precond n) : Prop :=
  ValidOutput result ∧
  ((StringToNat n % 4 = 0) ↔ (result = "4\n")) ∧
  ((StringToNat n % 4 ≠ 0) ↔ (result = "0\n"))

theorem solve_spec_satisfied (n : String) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  unfold solve_postcond solve ValidOutput
  constructor
  · -- Prove ValidOutput
    split_ifs
    · left; rfl
    · right; rfl
  constructor
  · -- Prove (StringToNat n % 4 = 0) ↔ (result = "4\n")
    constructor
    · intro h_div
      simp [h_div]
    · intro h_result
      split_ifs at h_result with h_cond
      · exact h_cond
      · simp at h_result
  · -- Prove (StringToNat n % 4 ≠ 0) ↔ (result = "0\n")
    constructor
    · intro h_not_div
      simp [h_not_div]
    · intro h_result
      split_ifs at h_result with h_cond
      · simp at h_result
      · exact h_cond
-- </vc-theorems>

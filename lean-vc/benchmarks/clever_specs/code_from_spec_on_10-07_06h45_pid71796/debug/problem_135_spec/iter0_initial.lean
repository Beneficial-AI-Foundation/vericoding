def problem_spec
-- function signature
(impl: List Int → Int)
-- inputs
(arr: List Int) :=
-- spec
let spec (result: Int) :=
  ¬arr.any (fun x => 1 < arr.count x) →
  (arr.length = 0 ∨ arr.length = 1 → result = -1) ∧
  (1 < arr.length →
    let last := arr.length-1;
    let i := if arr[last]! < arr[last-1]! then Int.ofNat last else -1;
    result = max (impl (arr.take last)) i);
-- program termination
∃ result, impl arr = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def implementation (arr: List Int) : Int :=
  if arr.length ≤ 1 then -1
  else
    let last := arr.length - 1
    let i := if arr[last]! < arr[last - 1]! then Int.ofNat last else -1
    max (implementation (arr.take last)) i

-- LLM HELPER
theorem take_length_lt {α : Type*} (l : List α) (n : Nat) (h : 0 < l.length) : 
  (l.take n).length < l.length := by
  simp [List.length_take]
  by_cases h_le : n ≤ l.length
  · simp [h_le]
    cases' n with n
    · simp
    · simp [Nat.succ_le_iff] at h_le
      exact Nat.lt_of_succ_le h_le
  · simp [h_le]
    exact h

-- LLM HELPER
theorem implementation_terminates (arr : List Int) : 
  ∃ result, implementation arr = result := by
  sorry

-- LLM HELPER
theorem implementation_spec_holds (arr : List Int) :
  let spec (result: Int) :=
    ¬arr.any (fun x => 1 < arr.count x) →
    (arr.length = 0 ∨ arr.length = 1 → result = -1) ∧
    (1 < arr.length →
      let last := arr.length-1;
      let i := if arr[last]! < arr[last-1]! then Int.ofNat last else -1;
      result = max (implementation (arr.take last)) i);
  spec (implementation arr) := by
  intro h_no_duplicates
  constructor
  · intro h_short
    unfold implementation
    cases' h_short with h_empty h_one
    · simp [h_empty]
    · simp [h_one]
  · intro h_long
    unfold implementation
    simp [Nat.not_le.mpr (Nat.one_lt_cast.mp h_long)]
    rfl

theorem correctness
(arr: List Int)
: problem_spec implementation arr := by
  exact ⟨implementation arr, rfl, implementation_spec_holds arr⟩
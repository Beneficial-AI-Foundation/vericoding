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

def implementation (arr: List Int) : Int :=
  if arr.length ≤ 1 then -1
  else
    let last := arr.length - 1
    let i := if arr[last]! < arr[last - 1]! then Int.ofNat last else -1
    max (implementation (arr.take last)) i
termination_by arr.length

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

theorem correctness
(arr: List Int)
: problem_spec implementation arr := by
  exact ⟨implementation arr, rfl, implementation_spec_holds arr⟩
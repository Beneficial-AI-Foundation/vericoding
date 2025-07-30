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
  if arr.length = 0 ∨ arr.length = 1 then
    -1
  else
    let last := arr.length - 1
    let i := if arr[last]! < arr[last - 1]! then Int.ofNat last else -1
    max (implementation (arr.take last)) i

-- LLM HELPER
lemma take_length_lt (arr: List Int) (h: 1 < arr.length) : (arr.take (arr.length - 1)).length < arr.length := by
  rw [List.length_take]
  simp only [min_def]
  split
  · assumption
  · omega

-- LLM HELPER
lemma take_preserves_no_duplicates (arr: List Int) : ¬arr.any (fun x => 1 < arr.count x) → ¬(arr.take (arr.length - 1)).any (fun x => 1 < (arr.take (arr.length - 1)).count x) := by
  intro h
  intro contra
  apply h
  rw [List.any_iff_exists] at contra ⊢
  obtain ⟨x, hx_mem, hx_count⟩ := contra
  use x
  constructor
  · exact List.mem_of_mem_take hx_mem
  · have h_take_count_le : (arr.take (arr.length - 1)).count x ≤ arr.count x := List.count_take_le x arr (arr.length - 1)
    omega

theorem correctness
(arr: List Int)
: problem_spec implementation arr := by
  unfold problem_spec
  use implementation arr
  constructor
  · rfl
  · intro h_no_dup
    constructor
    · intro h_short
      unfold implementation
      simp [h_short]
    · intro h_long
      unfold implementation
      simp [h_long]
      have h_rec : problem_spec implementation (arr.take (arr.length - 1)) := by
        apply correctness
      unfold problem_spec at h_rec
      obtain ⟨result, h_eq, h_spec⟩ := h_rec
      rw [←h_eq]
      rw [h_spec]
      · rfl
      · exact take_preserves_no_duplicates arr h_no_dup
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Nat) (seq : List Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_elements_in_original {n : Nat} {seq : List Nat} (h : seq.length > 0) :
  let result := solve n seq
  ∀ x, x ∈ result → x ∈ seq :=
sorry

theorem result_preserves_first_occurrences {n : Nat} {seq : List Nat} (h : seq.length > 0) :
  let result := solve n seq
  let firstOccurrences := seq.foldl (λ acc x => if x ∈ acc then acc else acc ++ [x]) []
  result = firstOccurrences :=
sorry

theorem result_length_bounded {n : Nat} {seq : List Nat} (h : seq.length > 0) :
  let result := solve n seq
  result.length ≤ seq.length :=
sorry

/-
info: [1, 2]
-/
-- #guard_msgs in
-- #eval solve 2 [1, 1, 2, 2]

/-
info: [1, 3, 4, 2]
-/
-- #guard_msgs in
-- #eval solve 4 [1, 3, 1, 4, 3, 4, 2, 2]

/-
info: [1, 2, 3]
-/
-- #guard_msgs in
-- #eval solve 3 [1, 2, 3, 1, 2, 3]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
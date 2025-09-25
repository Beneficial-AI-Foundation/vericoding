-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def word_subsets (A B: List String) : List String := sorry

def count_char (c: Char) (s: String) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem word_subsets_result_subset
  (A B: List String) 
  (result := word_subsets A B) :
  ∀ x, x ∈ result → x ∈ A := sorry

theorem word_subsets_letters_count
  (A B: List String) 
  (result := word_subsets A B) :
  ∀ w ∈ result, ∀ b_word ∈ B, ∀ letter : Char, 
  let max_count := (List.map (fun b => count_char letter b) B).maximum?
  match max_count with
  | some count => count_char letter w ≥ count
  | none => True := sorry

theorem word_subsets_single_word
  (w: String) :
  let result := word_subsets [w] [(w.get! 0).toString]
  (count_char (w.get! 0) w ≥ 1) →
  result = [w] := sorry

/-
info: sorted(['facebook', 'google', 'leetcode'])
-/
-- #guard_msgs in
-- #eval sorted word_subsets(A1, B1)

/-
info: sorted(['apple', 'google', 'leetcode'])
-/
-- #guard_msgs in
-- #eval sorted word_subsets(A2, B2)

/-
info: sorted(['facebook', 'leetcode'])
-/
-- #guard_msgs in
-- #eval sorted word_subsets(A3, B3)
-- </vc-theorems>
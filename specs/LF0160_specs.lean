-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_subsequence (s t : String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_string_is_subsequence {t : String} :
  is_subsequence "" t = true := sorry 

theorem string_is_subsequence_of_itself {s : String} :
  is_subsequence s s = true := sorry

theorem longer_string_not_subsequence {s t : String} :
  s.length > t.length → is_subsequence s t = false := sorry

theorem subsequence_in_concatenation {s t : String} :
  s ≠ "" → 
  is_subsequence s (s ++ t) = true ∧ is_subsequence s (t ++ s) = true := sorry

theorem inserting_chars_preserves_subsequence {s t : String} :
  s ≠ "" →
  (let result := String.intercalate t (s.data.map toString);
   is_subsequence s result = true) := sorry

theorem subsequence_maintains_order {s t : String} :
  s.length ≥ 2 →
  let reversed := String.mk s.data.reverse;
  s ≠ reversed →
  is_subsequence s t = true →
  is_subsequence reversed t = false := sorry
-- </vc-theorems>
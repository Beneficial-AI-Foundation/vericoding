-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_divisible_by_6 (s: String) : List String := sorry

theorem is_divisible_by_6_length_constraints {s : String} :
  s.length = 0 ∨ s.length > 10000 → is_divisible_by_6 s = [] := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem is_divisible_by_6_all_divisible {s : String} (h : s.length > 0) (h' : s.length ≤ 10000) :
  ∀ x ∈ is_divisible_by_6 s, (String.toNat! x) % 6 = 0 := sorry 

theorem is_divisible_by_6_sorted {s : String} (h : s.length > 0) (h' : s.length ≤ 10000) :
  ∀ i j, i < j → i < (is_divisible_by_6 s).length → j < (is_divisible_by_6 s).length → 
    (is_divisible_by_6 s)[i]! < (is_divisible_by_6 s)[j]! := sorry

theorem is_divisible_by_6_no_leading_zeros {s : String} (h : s.length > 0) (h' : s.length ≤ 10000) :
  ∀ x ∈ is_divisible_by_6 s, ¬String.startsWith x "0" := sorry
-- </vc-theorems>
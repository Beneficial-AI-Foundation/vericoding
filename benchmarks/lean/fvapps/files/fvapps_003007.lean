-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def group_by_commas (n : Nat) : String := sorry

theorem group_by_commas_only_digits_and_commas (n : Nat) : 
  ∀ c, c ∈ (group_by_commas n).data → 
    c = ',' ∨ c.isDigit := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem group_by_commas_preserves_value (n : Nat) :
  (group_by_commas n).replace "," "" = n.repr := sorry

theorem group_by_commas_groups_size {n : Nat} {s : List String} :
  s = (group_by_commas n).split (· = ',') →
  s ≠ [] →
  (∀ g ∈ s.tail, g.length = 3) ∧
  1 ≤ s.head!.length ∧ 
  s.head!.length ≤ 3 := sorry
-- </vc-theorems>
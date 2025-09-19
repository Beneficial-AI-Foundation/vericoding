-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (l : Nat) (s : String) : String := sorry

theorem solve_l1_maintains_length (s : String) (h : s.length > 0) : 
  (solve 1 s).length = s.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_l1_is_rotation (s : String) (h : s.length > 0) :
  ∃ i, i < s.length ∧ solve 1 s = s.drop i ++ s.take i := sorry

theorem solve_l1_is_lexmin (s : String) (h : s.length > 0) :
  ∀ i, i < s.length → solve 1 s ≤ (s.drop i ++ s.take i) := sorry

theorem solve_l1_same_chars (s : String) (h : s.length > 0) :
  ∀ c, (s.data.count c = (solve 1 s).data.count c) := sorry

theorem solve_general_maintains_length (l : Nat) (s : String) (hl : l ≥ 2) (hs : s.length > 0) :
  (solve l s).length = s.length := sorry

theorem solve_general_same_chars (l : Nat) (s : String) (hl : l ≥ 2) (hs : s.length > 0) :
  ∀ c, (s.data.count c = (solve l s).data.count c) := sorry

theorem solve_general_lexmin (l : Nat) (s : String) (hl : l ≥ 2) (hs : s.length > 0) :
  solve l s ≤ s := sorry

theorem solve_single_char (c : Char) (h : 'a' ≤ c ∧ c ≤ 'z') :
  solve 1 (String.mk [c]) = String.mk [c] ∧ 
  solve 2 (String.mk [c]) = String.mk [c] := sorry
-- </vc-theorems>
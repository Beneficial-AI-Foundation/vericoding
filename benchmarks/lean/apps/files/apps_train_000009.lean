def count_alice_score (s : String) : Nat :=
  sorry

def countOnes (s : String) : Nat :=
  sorry

def sortByLengthDesc (ls : List String) : List String :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def getAlternateSum (ls : List String) : Nat :=
  sorry

theorem result_not_exceed_input_length 
  (s : String) : 
  count_alice_score s ≤ s.length := 
  sorry

theorem result_nonnegative
  (s : String) :
  count_alice_score s ≥ 0 :=
  sorry

theorem empty_or_zeros_returns_zero
  (s : String) :
  (s.isEmpty ∨ s.all (· = '0')) → count_alice_score s = 0 :=
  sorry

theorem all_ones_full_score
  (s : String) :
  s.all (· = '1') →
  s.length > 0 →
  count_alice_score s = s.length :=
  sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_alice_score "01111001"

/-
info: 6
-/
-- #guard_msgs in
-- #eval count_alice_score "111111"

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_alice_score "101010101"

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
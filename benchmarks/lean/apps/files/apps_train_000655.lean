-- <vc-helpers>
-- </vc-helpers>

def BinaryString := String 

def compare_signatures (n m : Nat) (sig1 sig2 : List BinaryString) : Nat :=
  sorry

theorem compare_signatures_non_negative (n m : Nat) (sig1 sig2 : List BinaryString) :
  compare_signatures n m sig1 sig2 ≥ 0 :=
sorry

theorem compare_signatures_upper_bound (n m : Nat) (sig1 sig2 : List BinaryString) :
  compare_signatures n m sig1 sig2 ≤ n * m :=
sorry

theorem compare_signatures_identical (n m : Nat) (sig : List BinaryString) :
  compare_signatures n m sig sig = 0 :=
sorry

theorem compare_signatures_empty (n m : Nat) :
  let emptySignature := List.replicate n ("0")
  compare_signatures n m emptySignature emptySignature = 0 :=
sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval compare_signatures 3 3 ["100", "010", "000"] ["000", "010", "001"]

/-
info: 2
-/
-- #guard_msgs in
-- #eval compare_signatures 4 4 ["0000", "0110", "0000", "0011"] ["1100", "0000", "1100", "0000"]

/-
info: 1
-/
-- #guard_msgs in
-- #eval compare_signatures 3 3 ["100", "000", "001"] ["000", "010", "000"]

-- Apps difficulty: interview
-- Assurance level: guarded
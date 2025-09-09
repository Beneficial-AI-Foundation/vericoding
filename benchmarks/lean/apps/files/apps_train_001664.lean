def abs (n : Nat) : Nat :=
  sorry

def isValidPos (pos : String) : Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def knight (s e : String) : Nat :=
  sorry

theorem knight_valid_range {s e : String} 
  (h1 : isValidPos s) (h2 : isValidPos e) : 
  let m := knight s e
  0 ≤ m ∧ m ≤ 6 := 
  sorry

theorem knight_same_position {p : String}
  (h : isValidPos p) :
  knight p p = 0 :=
  sorry

theorem knight_diagonal_adjacent {s e : String}  
  (h1 : isValidPos s) (h2 : isValidPos e)
  (h3 : abs ((s.get! ⟨0⟩).toNat - (e.get! ⟨0⟩).toNat) = 1)
  (h4 : abs ((s.get! ⟨1⟩).toNat - (e.get! ⟨1⟩).toNat) = 1) :
  knight s e = 2 :=
  sorry

theorem knight_symmetric {p t : String}
  (h1 : isValidPos p) (h2 : isValidPos t) :
  knight p t = knight t p :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval knight "a3" "b5"

/-
info: 2
-/
-- #guard_msgs in
-- #eval knight "a1" "c5"

/-
info: 0
-/
-- #guard_msgs in
-- #eval knight "d5" "d5"

-- Apps difficulty: interview
-- Assurance level: guarded
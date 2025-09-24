-- <vc-preamble>
def List.sum (xs : List Nat) : Nat :=
  xs.foldl (· + ·) 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def luck_check (s : String) : Option Bool := sorry

theorem lucky_number_symmetry {n : Nat} : 
  n > 0 → let s := toString n;
  match luck_check s with
  | some true => 
      let leftHalf := s.take (s.length / 2);
      let rightHalf := s.drop ((s.length + 1) / 2);
      (leftHalf.toList.map Char.toNat).sum = (rightHalf.toList.map Char.toNat).sum
  | _ => True := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem lucky_number_numeric {s : String} :
  (∀ c ∈ s.data, c.isDigit) →
  s.length > 0 →
  (luck_check s).isSome := sorry

theorem non_numeric_input_none {s : String} :
  (∃ c ∈ s.data, !c.isDigit) →
  luck_check s = none := sorry

theorem empty_string_none :
  luck_check "" = none := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval luck_check "003111"

/-
info: True
-/
-- #guard_msgs in
-- #eval luck_check "17935"

/-
info: False
-/
-- #guard_msgs in
-- #eval luck_check "543970707"
-- </vc-theorems>
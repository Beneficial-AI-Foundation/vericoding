-- <vc-preamble>
def sumFracts (lst : List (Int × Nat)) : Option (Int ⊕ (Int × Nat)) := sorry

theorem sum_fracts_empty : 
  sumFracts [] = none := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def addFractions (f1 f2 : Fraction) : Fraction := sorry

theorem sum_fracts_preserves_value (lst : List (Int × Nat)) (h : ∀ p : Int × Nat, p ∈ lst → p.2 > 0) :
  match sumFracts lst with
  | none => lst = []
  | some (Sum.inl n) => Fraction.mk n 1 = lst.foldr (fun p acc => addFractions acc (Fraction.mk p.1 p.2)) (Fraction.mk 0 1)
  | some (Sum.inr (n,d)) => Fraction.mk n d = lst.foldr (fun p acc => addFractions acc (Fraction.mk p.1 p.2)) (Fraction.mk 0 1)
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_fracts_single (n : Int) (d : Nat) (h : d > 0) :
  sumFracts [(n,d)] = if d = 1 
    then some (Sum.inl n)
    else some (Sum.inr (n,d)) := sorry

theorem sum_fracts_result_form (lst : List (Int × Nat)) (h : ∀ p : Int × Nat, p ∈ lst → p.2 > 0) :
  match lst with
  | [] => sumFracts lst = none
  | _ => ∃ n d, (sumFracts lst = some (Sum.inl n) ∧ d = 1) ∨ 
                (sumFracts lst = some (Sum.inr (n,d)) ∧ d > 1)
  := sorry

/-
info: [13, 12]
-/
-- #guard_msgs in
-- #eval sum_fracts [[1, 2], [1, 3], [1, 4]]

/-
info: 2
-/
-- #guard_msgs in
-- #eval sum_fracts [[1, 3], [5, 3]]

/-
info: None
-/
-- #guard_msgs in
-- #eval sum_fracts []
-- </vc-theorems>
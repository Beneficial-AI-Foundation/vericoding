-- <vc-helpers>
-- </vc-helpers>

def calculate_milk_share (N M K : Nat) (A : List Nat) : Nat :=
  sorry

theorem milk_share_non_negative (N M K : Nat) (A : List Nat)
        (h1 : N > 0) (h2 : M > 0) (h3 : K > 0) (h4 : A.length > 0) :
  calculate_milk_share N M K A ≥ 0 := sorry

theorem milk_share_less_than_modulo (N M K : Nat) (A : List Nat) 
        (h1 : N > 0) (h2 : M > 0) (h3 : K > 0) (h4 : A.length > 0) :
  calculate_milk_share N M K A < 1000000007 := sorry

theorem milk_share_extension (N M K : Nat) (A : List Nat)
        (h1 : N > 0) (h2 : M > 0) (h3 : K > 0) (h4 : A.length > 0) :
  calculate_milk_share N M K (A ++ [0]) = calculate_milk_share N M K A := sorry

theorem milk_share_zero_array (N M K : Nat)
        (h1 : N > 0) (h2 : M > 0) (h3 : K > 0) :
  calculate_milk_share N M K (List.replicate N 0) = 0 := sorry

/-
info: 9
-/
-- #guard_msgs in
-- #eval calculate_milk_share 3 3 3 [15, 8, 10]

/-
info: 2
-/
-- #guard_msgs in
-- #eval calculate_milk_share 2 2 2 [5, 3]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
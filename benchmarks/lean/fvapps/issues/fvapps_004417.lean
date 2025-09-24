-- <vc-preamble>
def List.sum : List Int → Int 
  | [] => 0
  | x::xs => x + sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def beggars (values : List Int) (n : Nat) : List Int := sorry

def getNth (values : List Int) (n i : Nat) : Int :=
  match values with
  | [] => 0
  | x::xs => if i % n = 0 then x + getNth xs n (i+1) else getNth xs n (i+1)
-- </vc-definitions>

-- <vc-theorems>
theorem beggars_empty_for_zero_n 
  (values : List Int) :
  beggars values 0 = [] := sorry

theorem beggars_length_property 
  (values : List Int) (n : Nat) : 
  n > 0 → (beggars values n).length = n := sorry 

theorem beggars_sum_property 
  (values : List Int) (n : Nat) :
  n > 0 → List.sum values = List.sum (beggars values n) := sorry

theorem beggars_single_beggar_property
  (values : List Int) :
  values.length > 0 → beggars values 1 = [List.sum values] := sorry

theorem beggars_more_beggars_property
  (values : List Int) (n : Nat) :
  n > values.length →
  beggars values n = 
    beggars values values.length ++ List.replicate (n - values.length) 0 := sorry

/-
info: [15]
-/
-- #guard_msgs in
-- #eval beggars [1, 2, 3, 4, 5] 1

/-
info: [9, 6]
-/
-- #guard_msgs in
-- #eval beggars [1, 2, 3, 4, 5] 2

/-
info: [5, 7, 3]
-/
-- #guard_msgs in
-- #eval beggars [1, 2, 3, 4, 5] 3
-- </vc-theorems>
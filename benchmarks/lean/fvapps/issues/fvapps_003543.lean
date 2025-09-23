-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_valid_madhav_length (n : Nat) : Bool := sorry

def is_madhav_array (arr : List Int) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_element_array_is_false (x : Int) :
  is_madhav_array [x] = false := sorry

theorem invalid_length_arrays_are_false (arr : List Int) :
  ¬ is_valid_madhav_length arr.length →
  is_madhav_array arr = false := sorry

theorem valid_madhav_arrays (k : Nat) (h : k ≥ 2) :
  let total_len := k * (k + 1) / 2
  let zeros := List.replicate (k * (k + 1) / 2 - k) 0
  let ks := List.replicate k k
  let arr := zeros.map Int.ofNat ++ ks.map Int.ofNat
  is_madhav_array arr = true := sorry

theorem invalid_madhav_arrays_different_sums (k : Nat) (h : k ≥ 2) :
  let make_arr : Nat → List Int := λ i => 
    if i = 0 then [Int.ofNat (k + i)]
    else List.replicate i (Int.ofNat 0) ++ [Int.ofNat (k + i)]
  let arr := List.join (List.map make_arr (List.range k))
  is_madhav_array arr = false := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_madhav_array [6, 2, 4, 2, 2, 2, 1, 5, 0, 0]

/-
info: False
-/
-- #guard_msgs in
-- #eval is_madhav_array [5, 2, 4, 1, 0, 3]

/-
info: False
-/
-- #guard_msgs in
-- #eval is_madhav_array [1]
-- </vc-theorems>
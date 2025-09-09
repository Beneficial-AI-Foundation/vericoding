def isPowerOfTwo (n : Nat) : Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def arrayConversion (arr : List Nat) : Nat :=
  sorry

theorem array_conversion_power_of_two_length
  {n : Nat} {arr : List Nat}
  (h1 : n ≥ 1) (h2 : n ≤ 5)
  (h3 : arr.length = 2^n) :
  isPowerOfTwo arr.length = true ∧ 
  arrayConversion arr ≥ 0 :=
sorry

theorem array_conversion_deterministic 
  {arr : List Nat} 
  (h : isPowerOfTwo arr.length = true) :
  arrayConversion arr = arrayConversion arr :=
sorry

theorem array_conversion_monotonic
  {arr : List Nat} {i : Nat}
  (h1 : isPowerOfTwo arr.length = true)
  (h2 : i < arr.length) :
  let arr' := arr.set i (arr[i] + 1)
  arrayConversion arr' ≥ arrayConversion arr :=
sorry

/-
info: 186
-/
-- #guard_msgs in
-- #eval array_conversion [1, 2, 3, 4, 5, 6, 7, 8]

/-
info: 64
-/
-- #guard_msgs in
-- #eval array_conversion [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

/-
info: 60
-/
-- #guard_msgs in
-- #eval array_conversion [3, 3, 5, 5]

-- Apps difficulty: introductory
-- Assurance level: unguarded
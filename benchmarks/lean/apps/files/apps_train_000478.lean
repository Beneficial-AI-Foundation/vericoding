-- <vc-preamble>
def max_width_ramp (nums : List Int) : Nat :=
  sorry

def isSorted (l : List Int) : Bool :=
  match l with
  | [] => true 
  | [_] => true
  | x::y::rest => x ≤ y && isSorted (y::rest)

def isStrictlyDecreasing (l : List Int) : Bool :=
  match l with
  | [] => true
  | [_] => true
  | x::y::rest => x > y && isStrictlyDecreasing (y::rest)
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hasNoDups (l : List Int) : Bool :=
  match l with
  | [] => true
  | x::xs => !(xs.contains x) && hasNoDups xs
-- </vc-definitions>

-- <vc-theorems>
theorem max_width_ramp_non_negative (nums : List Int) :
  max_width_ramp nums ≥ 0 := 
  sorry

theorem max_width_ramp_upper_bound (nums : List Int) :
  max_width_ramp nums ≤ max 0 (nums.length - 1) :=
  sorry 

theorem max_width_ramp_small_lists (nums : List Int) :
  nums.length ≤ 1 → max_width_ramp nums = 0 :=
  sorry

theorem max_width_ramp_valid_ramp_exists (nums : List Int) (h : max_width_ramp nums > 0) :
  ∃ i j, ∃ (hi : i < nums.length) (hj : j < nums.length),
         i < j ∧ j - i ≥ max_width_ramp nums ∧ 
         (nums.get ⟨i, hi⟩) ≤ (nums.get ⟨j, hj⟩) :=
  sorry

theorem max_width_ramp_monotonic_increasing (nums : List Int) :
  nums.length > 1 →
  isSorted nums = true →
  max_width_ramp nums = nums.length - 1 :=
  sorry

theorem max_width_ramp_strictly_decreasing (nums : List Int) :
  nums.length > 0 →
  isStrictlyDecreasing nums = true →
  hasNoDups nums = true →
  max_width_ramp nums = 0 :=
  sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval max_width_ramp [6, 0, 8, 2, 1, 5]

/-
info: 7
-/
-- #guard_msgs in
-- #eval max_width_ramp [9, 8, 1, 0, 1, 9, 4, 0, 4, 1]

/-
info: 0
-/
-- #guard_msgs in
-- #eval max_width_ramp [1, 0]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded
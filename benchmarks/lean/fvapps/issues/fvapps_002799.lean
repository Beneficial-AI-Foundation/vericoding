-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def add (nums : List Float) : Int := sorry

theorem add_returns_int (nums : List Float) :
  add nums = add nums := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem add_empty_list :
  add [] = 0 := sorry

theorem add_single_number (x : Float) :
  add [x] = Int.ofNat (x.toUInt64.toNat) := sorry 

theorem add_weighted_sum (nums : List Float) (h : nums ≠ []) :
  ∃ w : Float, w = (nums.enum.foldl (fun acc p => acc + p.2/(Float.ofNat (p.1 + 1))) 0) ∧ 
  (w - Float.ofInt (add nums)).abs < 0.01 := sorry

/-
info: 300
-/
-- #guard_msgs in
-- #eval add 100 200 300

/-
info: 2
-/
-- #guard_msgs in
-- #eval add 2

/-
info: 2
-/
-- #guard_msgs in
-- #eval add 4 -3 -2
-- </vc-theorems>
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bin_str (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem bin_str_nonnegative (s : String) (h : s.length > 0) :
  bin_str s ≥ 0 := sorry

theorem bin_str_ends_zero (s : String) (h : s.length > 0) (h2 : s.data.getLast! = '0') :
  bin_str s % 2 = 0 := sorry

theorem bin_str_ends_one (s : String) (h : s.length > 0) (h2 : s.data.getLast! = '1') :
  bin_str s % 2 = 1 := sorry

theorem bin_str_upper_bound (s : String) (h : s.length > 0) :
  bin_str s ≤ 2 * s.length - 1 := sorry

theorem bin_str_n_zeros (n : Nat) (h : n > 0) :
  bin_str (String.mk (List.replicate n '0')) = 0 := sorry

theorem bin_str_alternating (n : Nat) (h : n > 0) :
  bin_str (String.mk (List.join (List.replicate n ['1', '0']))) = 2 * n := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval bin_str "0101"

/-
info: 2
-/
-- #guard_msgs in
-- #eval bin_str "10000"

/-
info: 0
-/
-- #guard_msgs in
-- #eval bin_str "0000000000"
-- </vc-theorems>
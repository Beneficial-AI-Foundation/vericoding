-- <vc-preamble>
def sumList : List Nat → Nat 
  | [] => 0
  | x :: xs => x + sumList xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_the_difference (s t : String) : Char := sorry

theorem find_difference_finds_added_char (s : String) (extra_char : Char) :
  find_the_difference s (s.push extra_char) = extra_char := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_difference_order_independent (s : String) (t : String) (extra_char : Char) 
    (h : t = s.push extra_char) :
  ∀ perm : String, Perm t perm → find_the_difference s perm = extra_char := sorry

theorem find_difference_empty_source (c : Char) :
  find_the_difference "" (String.mk [c]) = c := sorry

theorem find_difference_ord_sum (s : String) (extra_char : Char) :
  let t := s.push extra_char
  Char.toNat (find_the_difference s t) = 
    sumList (t.data.map Char.toNat) - sumList (s.data.map Char.toNat) := sorry

/-
info: 'e'
-/
-- #guard_msgs in
-- #eval find_the_difference "abcd" "abcde"

/-
info: 'y'
-/
-- #guard_msgs in
-- #eval find_the_difference "" "y"

/-
info: '2'
-/
-- #guard_msgs in
-- #eval find_the_difference "hello" "hello2"
-- </vc-theorems>
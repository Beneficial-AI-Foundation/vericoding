-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_big_groups (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_big_groups_nonnegative (s : String) :
  count_big_groups s ≥ 0 :=
  sorry

theorem single_chars_give_zero (s : String) :
  List.Nodup s.data → count_big_groups s = 0 :=
  sorry  

theorem single_repeat_gives_zero (s : String) (c : Char) :
  s.data = List.replicate s.length c → count_big_groups s = 0 :=
  sorry

theorem short_strings_give_zero (s : String) :
  s.length ≤ 3 → count_big_groups s = 0 :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_big_groups "ccccoodeffffiiighhhhhhhhhhttttttts"

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_big_groups "soooooldieeeeeer"

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_big_groups "gztxxxxxggggggggggggsssssssbbbbbeeeeeeehhhmmmmmmmitttttttlllllhkppppp"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
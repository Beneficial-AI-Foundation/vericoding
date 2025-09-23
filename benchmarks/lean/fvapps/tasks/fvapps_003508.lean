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
-- </vc-theorems>
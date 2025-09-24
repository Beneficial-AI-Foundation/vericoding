-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Town := String
def countDeafRats (t : Town) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem non_negative_count : ∀ (t : Town),
  countDeafRats t ≥ 0 :=
  sorry

theorem count_below_total : ∀ (t : Town) (n : Nat),
  countDeafRats t ≤ n :=
  sorry

theorem spaces_dont_matter : ∀ (t1 t2 : Town),
  countDeafRats t1 = countDeafRats t2 :=
  sorry

theorem single_rat_direction : ∀ (t : Town) (r : RatPair),
  countDeafRats t ≤ 1 :=
  sorry

theorem empty_town_count :  
  countDeafRats "P" = 0 :=
  sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_deaf_rats "~O~O~O~O P"

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_deaf_rats "P O~ O~ ~O O~"

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_deaf_rats "~O~O~O~OP~O~OO~"
-- </vc-theorems>
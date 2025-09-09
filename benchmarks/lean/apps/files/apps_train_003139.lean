-- <vc-helpers>
-- </vc-helpers>

def strings_crossover (arr : List String) (result : String) : Nat :=
  sorry

theorem strings_crossover_non_negative (arr : List String) (result : String) :
  strings_crossover arr result ≥ 0 :=
sorry

theorem strings_crossover_max_pairs (arr : List String) (result : String) : 
  strings_crossover arr result ≤ (arr.length * (arr.length - 1)) / 2 :=
sorry

theorem strings_crossover_length_mismatch (arr : List String) (result : String) :
  (arr.head?.map String.length ≠ some result.length) →
  strings_crossover arr result = 0 :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval strings_crossover ["abc", "aaa", "aba", "bab"] "bbb"

/-
info: 0
-/
-- #guard_msgs in
-- #eval strings_crossover ["aacccc", "bbcccc"] "abdddd"

/-
info: 4
-/
-- #guard_msgs in
-- #eval strings_crossover ["a", "b", "c", "d", "e"] "c"

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
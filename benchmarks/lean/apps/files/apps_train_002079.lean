-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_distinct_or_values (nums : List Nat) : Nat := sorry

def uniqueCount (l : List Nat) : Nat := 
  (l.foldl (fun acc x => if x ∈ acc then acc else x::acc) []).length
-- </vc-definitions>

-- <vc-theorems>
theorem count_distinct_or_values_singleton {n : Nat} :
  count_distinct_or_values [n] = 1 := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_distinct_or_values [1, 2, 0]

/-
info: 11
-/
-- #guard_msgs in
-- #eval count_distinct_or_values [1, 2, 3, 4, 5, 6, 1, 2, 9, 10]

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_distinct_or_values [123]
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_roads_to_destroy (n : Nat) (edges : List (Nat × Nat)) (s1 t1 l1 s2 t2 l2 : Nat) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_bounds (n : Nat) (edges : List (Nat × Nat)) (s1 t1 l1 s2 t2 l2 : Nat) :
  let result := max_roads_to_destroy n edges s1 t1 l1 s2 t2 l2
  result = -1 ∨ (0 ≤ result ∧ result ≤ edges.length) :=
sorry

theorem identical_paths (n : Nat) (edges : List (Nat × Nat)) (s1 t1 l1 s2 t2 l2 : Nat) :
  max_roads_to_destroy n edges s1 t1 l1 s2 t2 l2 = 
  max_roads_to_destroy n edges s2 t2 l2 s1 t1 l1 :=
sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval max_roads_to_destroy 5 [(1, 2), (2, 3), (3, 4), (4, 5)] 1 3 2 3 5 2

/-
info: 1
-/
-- #guard_msgs in
-- #eval max_roads_to_destroy n edges 1 3 2 2 4 2

/-
info: -1
-/
-- #guard_msgs in
-- #eval max_roads_to_destroy n edges 1 3 2 3 5 1
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: unguarded
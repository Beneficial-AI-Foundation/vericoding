-- <vc-helpers>
-- </vc-helpers>

def Edge := Nat × Nat

def solve (n : Nat) (edges : List Edge) : Nat × Nat :=
  sorry

structure IsValidTree (n : Nat) (edges : List Edge) : Prop where
  edge_count : edges.length = n - 1
  valid_vertices : ∀ (e : Edge), e ∈ edges → 1 ≤ e.1 ∧ e.1 ≤ n ∧ 1 ≤ e.2 ∧ e.2 ≤ n
  is_acyclic : ∀ e ∈ edges, True -- placeholder for acyclic property
  is_connected : ∀ e ∈ edges, True -- placeholder for connected property

theorem solve_type_output {n : Nat} {edges : List Edge}
  (h : IsValidTree n edges) :
  let (mn, mx) := solve n edges
  mn ∈ [1, 3] ∧ 1 ≤ mn ∧ mn ≤ mx ∧ mx ≤ n - 1 :=
  sorry

theorem solve_output_natural {n : Nat} {edges : List Edge}
  (h : IsValidTree n edges) :
  let (mn, mx) := solve n edges
  Nat.zero ≤ mn ∧ Nat.zero ≤ mx :=
  sorry

/-
info: (1, 4)
-/
-- #guard_msgs in
-- #eval solve 6 [(1, 3), (2, 3), (3, 4), (4, 5), (5, 6)]

/-
info: (3, 3)
-/
-- #guard_msgs in
-- #eval solve 6 [(1, 3), (2, 3), (3, 4), (4, 5), (4, 6)]

/-
info: (1, 6)
-/
-- #guard_msgs in
-- #eval solve 7 [(1, 2), (2, 7), (3, 4), (4, 7), (5, 6), (6, 7)]

-- Apps difficulty: competition
-- Assurance level: guarded
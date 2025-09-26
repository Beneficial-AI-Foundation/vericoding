-- <vc-preamble>
def manhattan_distance (p1 p2 : Point) : Nat :=
  let dx := (p1.x - p2.x).toNat
  let dy := (p1.y - p2.y).toNat
  dx + dy

def euclidean_distance (p1 p2 : Point) : Float :=
  let dx := (p1.x - p2.x).toNat.toFloat
  let dy := (p1.y - p2.y).toNat.toFloat
  Float.sqrt (dx * dx + dy * dy)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_min_distance (n : Nat) (points : List Point) : Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_distance_nonnegativity {n : Nat} {points : List Point}
  (h1 : n ≥ 2)
  (h2 : points.length = n)
  (h3 : points.Nodup) :
  solve_min_distance n points ≥ 0 :=
sorry

theorem min_distance_euclidean_bound {n : Nat} {points : List Point} 
  (h1 : n ≥ 2)
  (h2 : points.length = n)
  (h3 : points.Nodup) :
  ∀ (i j : Fin points.length), i ≠ j →
  solve_min_distance n points ≤ euclidean_distance (points.get i) (points.get j) / Float.sqrt 2 + 0.000001 :=
sorry

theorem two_points_special_case {points : List Point}
  (h1 : points.length = 2)
  (h2 : points.Nodup)
  (h3 : points.get ⟨0, h1.symm ▸ Nat.zero_lt_succ 1⟩ = ⟨x₁, y₁⟩)
  (h4 : points.get ⟨1, h1.symm ▸ Nat.succ_lt_succ (Nat.zero_lt_succ 0)⟩ = ⟨x₂, y₂⟩)
  (h5 : x₁ = x₂ ∨ y₁ = y₂) :
  (solve_min_distance 2 points - (manhattan_distance ⟨x₁, y₁⟩ ⟨x₂, y₂⟩).toFloat / 2) ≤ 0.000001 ∧
  ((manhattan_distance ⟨x₁, y₁⟩ ⟨x₂, y₂⟩).toFloat / 2 - solve_min_distance 2 points) ≤ 0.000001 :=
sorry
-- </vc-theorems>
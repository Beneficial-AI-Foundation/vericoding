-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def IsTriangle (x y z : Nat) : Prop := x > 0 ∧ y > 0 ∧ z > 0

def polygon_cut (n : Nat) (triangles : List (Nat × Nat × Nat)) : (List Nat × List Nat) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem polygon_cut_output_lengths {n : Nat} {triangles : List (Nat × Nat × Nat)} 
  (h1 : n ≥ 3) : 
  let (vertices, cuts) := polygon_cut n triangles
  (vertices.length = n) ∧ (cuts.length = n - 2) := sorry

theorem polygon_cut_valid_vertices {n : Nat} {triangles : List (Nat × Nat × Nat)} 
  (h1 : n ≥ 3) :
  let (vertices, _) := polygon_cut n triangles;
  let expected := List.range n |> List.map (·+1)
  List.all vertices (fun v => v ≥ 1 ∧ v ≤ n) := sorry

theorem polygon_cut_valid_cuts {n : Nat} {triangles : List (Nat × Nat × Nat)} 
  (h1 : n ≥ 3) :
  let (_, cuts) := polygon_cut n triangles
  (∀ c ∈ cuts, 1 ≤ c ∧ c ≤ triangles.length) ∧ List.Nodup cuts := sorry

theorem polygon_cut_fan_triangulation {n : Nat} 
  (h1 : n ≥ 3) :
  let triangles := List.range (n-2) |> List.map (fun i => (1, i+2, i+3))
  let (vertices, cuts) := polygon_cut n triangles
  (vertices.length = n) ∧ (cuts.length = n-2) ∧ vertices.head? = some 1 := sorry
-- </vc-theorems>
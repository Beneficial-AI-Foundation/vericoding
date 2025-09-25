-- <vc-preamble>
def List.sum (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: xs => x + xs.sum

def find_min_max_traffic (n: Nat) (traffic: List Nat) (edges: List (Nat × Nat)) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def abs (n : Nat) : Nat :=
  n
-- </vc-definitions>

-- <vc-theorems>
theorem min_max_traffic_bounds {n: Nat} {traffic: List Nat} {edges: List (Nat × Nat)}
  (h₁: n ≥ 3)
  (h₂: traffic.length = n)
  (h₃: edges.length = n - 1) :
  let result := find_min_max_traffic n traffic edges
  result ≤ traffic.sum ∧ 
  result ≥ Option.get! (List.maximum? traffic) ∧
  result * 3 ≥ traffic.sum := by
  sorry

theorem min_max_traffic_symmetric {n: Nat} {traffic: List Nat} {edges: List (Nat × Nat)} 
  (h₁: n ≥ 3)
  (h₂: traffic.length = n)
  (h₃: edges.length = n - 1) :
  let reversed_edges := edges.map (fun (e: Nat × Nat) => (e.2, e.1))
  find_min_max_traffic n traffic edges = find_min_max_traffic n traffic reversed_edges := by
  sorry

theorem min_max_traffic_balanced_line {n: Nat}
  (h: n ≥ 3) :
  let traffic := List.replicate n 100
  let edges := (List.range (n-1)).map (fun i => (i+1, i+2))
  let result := find_min_max_traffic n traffic edges
  let expected := (n * 100) / 3
  abs (result - expected) ≤ 100 := by
  sorry
-- </vc-theorems>
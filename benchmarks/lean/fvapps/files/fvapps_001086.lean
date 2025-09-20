-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_delivery_problem (n m : Nat) (roads : List (Nat × Nat)) (deliveries : List (Nat × Nat)) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem delivery_reflexive {n m : Nat} {roads : List (Nat × Nat)} {i : Nat} (h : i < n) :
  (solve_delivery_problem n m roads [(i,i)]).head! = "YO" :=
  sorry

theorem delivery_symmetric {n m : Nat} {roads : List (Nat × Nat)} {x y : Nat} 
  (hx : x < n) (hy : y < n) :
  solve_delivery_problem n m roads [(x,y)] = solve_delivery_problem n m roads [(y,x)] :=
  sorry

theorem empty_roads_only_self_reachable {n : Nat} {i j : Nat} (hi : i < n) (hj : j < n) :
  solve_delivery_problem n 0 [] [(i,j)] = ["YO"] ↔ i = j :=
  sorry

theorem valid_output_format {n m : Nat} {roads : List (Nat × Nat)} {x y : Nat} 
  (hx : x < n) (hy : y < n) :
  (solve_delivery_problem n m roads [(x,y)]).head! = "YO" ∨ 
  (solve_delivery_problem n m roads [(x,y)]).head! = "NO" :=
  sorry
-- </vc-theorems>
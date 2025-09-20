-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Tree := List (Nat × Nat)

def solve_tree_game (n : Nat) (edges : Tree) : Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem tree_game_positive (n : Nat) (edges : Tree) :
  n ≥ 2 → solve_tree_game n edges > 0 :=
  sorry

theorem tree_game_min (n : Nat) (edges : Tree) :
  n ≥ 2 → solve_tree_game n edges ≥ 1 :=
  sorry

theorem tree_game_max (n : Nat) (edges : Tree) :
  n ≥ 2 → solve_tree_game n edges ≤ Float.ofNat n :=
  sorry

theorem line_graph_expected (n : Nat) :
  n ≥ 2 →
  let edges := List.range (n-1) |> List.map (fun i => (i+1, i+2));
  let expected := List.range n |> List.map (fun i => 1.0/(Float.ofNat (i+1))) |> List.foldl Float.add 0;
  Float.abs (solve_tree_game n edges - expected) < 0.000001 :=
  sorry
-- </vc-theorems>
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countSeparatedCityPairs (n : Nat) (m : Nat) (a : Nat) (b : Nat) (edges : List (Nat × Nat)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem countSeparatedCityPairs_result_nonneg (n m a b : Nat) (edges : List (Nat × Nat)) 
    (hn : n ≥ 2) (ha : a ≤ n) (hb : b ≤ n) (hab : a ≠ b) :
    countSeparatedCityPairs n m a b edges ≥ 0 := sorry

theorem countSeparatedCityPairs_upper_bound (n m a b : Nat) (edges : List (Nat × Nat))
    (hn : n ≥ 2) (ha : a ≤ n) (hb : b ≤ n) (hab : a ≠ b) :
    countSeparatedCityPairs n m a b edges ≤ (n-2) * (n-2) := sorry

theorem countSeparatedCityPairs_empty_graph (n m a b : Nat) (edges : List (Nat × Nat))
    (hn : n ≥ 2) (ha : a ≤ n) (hb : b ≤ n) (hab : a ≠ b)
    (he : edges = []) :
    countSeparatedCityPairs n m a b edges ≥ 0 := sorry

theorem countSeparatedCityPairs_sparse_graph (n m a b : Nat) (edges : List (Nat × Nat))
    (hn : n ≥ 2) (ha : a ≤ n) (hb : b ≤ n) (hab : a ≠ b)
    (hm : m < n-1) :
    countSeparatedCityPairs n m a b edges ≥ 0 := sorry

theorem countSeparatedCityPairs_path_graph (n : Nat) (hn : n ≥ 2) :
  let edges := List.range (n-1) |>.map (fun i => (i+1, i+2))
  let m := n-1
  let a := 1
  let b := n 
  countSeparatedCityPairs n m a b edges ≥ 0 ∧
  countSeparatedCityPairs n m a b edges ≤ (n-2) * (n-2) := sorry

theorem countSeparatedCityPairs_complete_graph (n a b : Nat)
    (hn : n ≥ 3) (ha : a ≤ n) (hb : b ≤ n) (hab : a ≠ b) :
  let edges := List.join (List.range n |>.map (fun i => 
                List.range (n-i) |>.map (fun j => (i+1, i+j+2))))
  let m := (n * (n-1)) / 2
  countSeparatedCityPairs n m a b edges = 0 := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_separated_city_pairs 7 7 3 5 [(1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 5)]

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_separated_city_pairs 4 5 2 3 [(1, 2), (2, 3), (3, 4), (4, 1), (4, 2)]

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_separated_city_pairs 4 3 2 1 [(1, 2), (2, 3), (4, 1)]
-- </vc-theorems>
/-
There are $n$ cities in Berland and some pairs of them are connected by two-way roads. It is guaranteed that you can pass from any city to any other, moving along the roads. Cities are numerated from $1$ to $n$.

Two fairs are currently taking place in Berland — they are held in two different cities $a$ and $b$ ($1 \le a, b \le n$; $a \ne b$).

Find the number of pairs of cities $x$ and $y$ ($x \ne a, x \ne b, y \ne a, y \ne b$) such that if you go from $x$ to $y$ you will have to go through both fairs (the order of visits doesn't matter). Formally, you need to find the number of pairs of cities $x,y$ such that any path from $x$ to $y$ goes through $a$ and $b$ (in any order).

Print the required number of pairs. The order of two cities in a pair does not matter, that is, the pairs $(x,y)$ and $(y,x)$ must be taken into account only once.

-----Input-----

The first line of the input contains an integer $t$ ($1 \le t \le 4\cdot10^4$) — the number of test cases in the input. Next, $t$ test cases are specified.

The first line of each test case contains four integers $n$, $m$, $a$ and $b$ ($4 \le n \le 2\cdot10^5$, $n - 1 \le m \le 5\cdot10^5$, $1 \le a,b \le n$, $a \ne b$) — numbers of cities and roads in Berland and numbers of two cities where fairs are held, respectively.

The following $m$ lines contain descriptions of roads between cities. Each of road description contains a pair of integers $u_i, v_i$ ($1 \le u_i, v_i \le n$, $u_i \ne v_i$) — numbers of cities connected by the road.

Each road is bi-directional and connects two different cities. It is guaranteed that from any city you can pass to any other by roads. There can be more than one road between a pair of cities.

The sum of the values of $n$ for all sets of input data in the test does not exceed $2\cdot10^5$. The sum of the values of $m$ for all sets of input data in the test does not exceed $5\cdot10^5$.

-----Output-----

Print $t$ integers — the answers to the given test cases in the order they are written in the input.

-----Example-----
Input
3
7 7 3 5
1 2
2 3
3 4
4 5
5 6
6 7
7 5
4 5 2 3
1 2
2 3
3 4
4 1
4 2
4 3 2 1
1 2
2 3
4 1

Output
4
0
1
-/

-- <vc-helpers>
-- </vc-helpers>

def countSeparatedCityPairs (n : Nat) (m : Nat) (a : Nat) (b : Nat) (edges : List (Nat × Nat)) : Nat :=
  sorry

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

-- Apps difficulty: competition
-- Assurance level: guarded
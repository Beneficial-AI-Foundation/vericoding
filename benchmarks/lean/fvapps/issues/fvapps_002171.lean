-- <vc-preamble>
def UnionFind.new (n : Nat) : UnionFind := sorry
def UnionFind.isConnected (uf : UnionFind) (x y : Nat) : Bool := sorry

def UnionFind.unite (uf : UnionFind) (x y : Nat) : UnionFind := sorry
def solve (n m : Nat) (p : List Nat) (swaps : List (Nat × Nat)) : Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isValidPerm (arr : List Nat) : Bool := sorry

theorem solve_permutation_property (p : List Nat) 
  (h1 : p.length ≤ 20) (h2 : p.length > 0)
  (h3 : isValidPerm (p.map (·-1)) = true) :
  let n := p.length;
  let result := solve n 0 p [];
  0 ≤ result ∧ result ≤ n := by sorry
-- </vc-definitions>

-- <vc-theorems>
theorem UnionFind_init (n : Nat) (h : 0 < n) (h2 : n ≤ 100) :
  let uf := UnionFind.new n;
  Array.size (UnionFind.size uf) = n ∧ 
  Array.size (UnionFind.parent uf) = n ∧
  (∀ i, i < n → (UnionFind.size uf)[i]! = 1) ∧
  (∀ i, i < n → (UnionFind.parent uf)[i]! = i) := by sorry

theorem UnionFind_reflexive (n : Nat) (h : 0 < n) (h2 : n ≤ 100) :
  let uf := UnionFind.new n;
  ∀ i, i < n → UnionFind.isConnected uf i i = true := by sorry

theorem UnionFind_symmetry (n : Nat) (h : 1 < n) (h2 : n ≤ 100) :
  let uf := UnionFind.new n;
  ∀ i, i < n-1 → 
    let uf' := UnionFind.unite uf i (i+1);
    UnionFind.isConnected uf' i (i+1) = true ∧ 
    UnionFind.isConnected uf' (i+1) i = true := by sorry

theorem solve_no_swaps (n m : Nat) (h1 : 0 < n) (h2 : n ≤ 20) (h3 : m ≤ 10) :
  let p := List.range n;
  let swaps := [];
  solve n m (p.map (·+1)) swaps = n := by sorry

theorem solve_valid_swaps (n : Nat) (swaps : List (Nat × Nat)) 
  (h1 : 0 < n) (h2 : n ≤ 20) (h3 : swaps.length ≤ 10) :
  let p := List.range n |>.map (·+1);
  let result := solve n swaps.length p swaps;
  0 ≤ result ∧ result ≤ n := by sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve 5 2 #[5, 3, 1, 4, 2] #[(1, 3), (5, 4)]

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve 3 2 #[3, 2, 1] #[(1, 2), (2, 3)]

/-
info: 5
-/
-- #guard_msgs in
-- #eval solve 5 1 #[1, 2, 3, 4, 5] #[(1, 5)]
-- </vc-theorems>
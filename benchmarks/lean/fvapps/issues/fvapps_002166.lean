-- <vc-preamble>
def initTree (M : Nat) : LazySegmentTree M := sorry
def updateTree (M : Nat) : LazySegmentTree M → Nat → Nat → Int → LazySegmentTree M := sorry

def queryTree (M : Nat) : LazySegmentTree M → Nat → Nat → Int := sorry

def LV : Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def N0 : Nat := sorry
def INF : Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem lst_initialization_invariants {M : Nat} (h : M > 0) (h2 : M ≤ 100) :
  N0 = 2^LV ∧ N0 > 0 := by sorry

theorem segment_tree_operations_sound {M : Nat} (l r : Nat) (x : Int)
  (h1 : l ≤ r) (h2 : r < M) (h3 : M > 0)
  (h4 : l ≤ 10) (h5 : r ≤ 10) (h6 : x ≥ -100) (h7 : x ≤ 100) :
  let lst := initTree M
  let lst' := updateTree M lst l r x
  let result := queryTree M lst' l r 
  x ≥ 0 → result ≤ INF := by sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve 4 4 [(0, 3), (2, 3), (1, 3), (3, 4)]

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve 7 6 [(0, 7), (1, 5), (3, 6), (2, 7), (1, 6), (2, 6), (3, 7)]

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve 3 1 [(1, 2), (1, 2), (1, 2)]
-- </vc-theorems>
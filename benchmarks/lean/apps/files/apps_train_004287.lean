def abs (n : Int) : Nat :=
  if n ≥ 0 then n.toNat else (-n).toNat

-- <vc-helpers>
-- </vc-helpers>

def side_len (x y : Nat) : List Nat := sorry

def isSorted (l : List Nat) : Prop :=
  ∀ i j, i < j → j < l.length → 
    match l.get? i, l.get? j with
    | some vi, some vj => vi ≤ vj
    | _, _ => True

theorem triangle_inequality {x y : Nat} (h1 : x > 0) (h2 : y > 0) (z : Nat) 
  (h3 : z ∈ side_len x y) :
  z < x + y ∧ 
  x < y + z ∧ 
  y < x + z ∧ 
  z > (if x ≥ y then x - y else y - x) := sorry

theorem no_pythagorean_triples {x y : Nat} (h1 : x > 0) (h2 : y > 0) (z : Nat) 
  (h3 : z ∈ side_len x y) :
  z * z ≠ (if x * x ≥ y * y then x * x - y * y else y * y - x * x) ∧
  z * z ≠ x * x + y * y := sorry

theorem symmetric {x y : Nat} (h1 : x > 0) (h2 : y > 0) :
  side_len x y = side_len y x := sorry

/-
info: [1]
-/
-- #guard_msgs in
-- #eval side_len 1 1

/-
info: [2, 3, 4, 6]
-/
-- #guard_msgs in
-- #eval side_len 3 4

/-
info: [3, 4, 5, 6, 7, 8, 9]
-/
-- #guard_msgs in
-- #eval side_len 4 6

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
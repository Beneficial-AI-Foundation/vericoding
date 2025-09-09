def min_rounds_needed (n : Nat) (rounds : List Nat) : Nat := sorry

def list_maximum (l : List Nat) : Nat := 
  match l with
  | [] => 0
  | (x::xs) => xs.foldl Nat.max x

-- <vc-helpers>
-- </vc-helpers>

def list_sum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | (x::xs) => x + list_sum xs

theorem min_rounds_needed_all_zeros {n : Nat}
  (h : n ≥ 2) : 
  let rounds := List.replicate n 0
  min_rounds_needed n rounds = (n-2) / (n-1) := sorry

theorem min_rounds_needed_equal_rounds {n : Nat} {x : Nat}
  (h1 : n ≥ 2)
  (h2 : x ≥ 1) :
  let rounds := List.replicate n x
  min_rounds_needed n rounds = max x ((n*x + n-2) / (n-1)) := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval min_rounds_needed 3 [3, 2, 2]

/-
info: 3
-/
-- #guard_msgs in
-- #eval min_rounds_needed 4 [2, 2, 2, 2]

/-
info: 1005000000
-/
-- #guard_msgs in
-- #eval min_rounds_needed 3 [1000000000, 1000000000, 10000000]

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible
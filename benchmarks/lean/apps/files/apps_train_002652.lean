def parameter (n : Nat) : Nat := sorry

def digits (n : Nat) : List Nat := sorry

def fromDigits (ds : List Nat) : Nat := sorry

def listSum (xs : List Nat) : Nat := 
  match xs with
  | [] => 0
  | x :: xs => x + listSum xs

-- <vc-helpers>
-- </vc-helpers>

def listProd (xs : List Nat) : Nat :=
  match xs with
  | [] => 1
  | x :: xs => x * listProd xs

theorem parameter_single_digit (d : Nat)
  (h : d > 0) 
  (h2 : d ≤ 9) :
  parameter d = d := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval parameter 22

/-
info: 120
-/
-- #guard_msgs in
-- #eval parameter 1234

/-
info: 378
-/
-- #guard_msgs in
-- #eval parameter 239

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
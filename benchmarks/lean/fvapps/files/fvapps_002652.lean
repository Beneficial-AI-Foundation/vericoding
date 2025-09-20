-- <vc-preamble>
def listSum (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: xs => x + listSum xs

def listProd (xs : List Nat) : Nat :=
  match xs with
  | [] => 1
  | x :: xs => x * listProd xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def fromDigits (ds : List Nat) : Nat := sorry

def parameter (n : Nat) : Nat :=
sorry

def digits (n : Nat) : List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem parameter_single_digit (d : Nat)
  (h : d > 0)
  (h2 : d ≤ 9) :
  parameter d = d :=
sorry
-- </vc-theorems>
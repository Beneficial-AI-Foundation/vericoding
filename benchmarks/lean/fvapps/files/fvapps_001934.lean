-- <vc-preamble>
def list_maximum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | (x::xs) => xs.foldl Nat.max x

def list_sum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | (x::xs) => x + list_sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_rounds_needed (n : Nat) (rounds : List Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_rounds_needed_all_zeros {n : Nat}
  (h : n ≥ 2) :
  let rounds := List.replicate n 0
  min_rounds_needed n rounds = (n-2) / (n-1) :=
sorry

theorem min_rounds_needed_equal_rounds {n : Nat} {x : Nat}
  (h1 : n ≥ 2)
  (h2 : x ≥ 1) :
  let rounds := List.replicate n x
  min_rounds_needed n rounds = max x ((n*x + n-2) / (n-1)) :=
sorry
-- </vc-theorems>
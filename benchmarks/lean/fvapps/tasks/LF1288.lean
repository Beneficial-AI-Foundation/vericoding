-- <vc-preamble>
def list_min (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x::xs => List.foldl min x xs

def list_sum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x::xs => x + list_sum xs

def list_take_last (n : Nat) (l : List Nat) : List Nat :=
  match n, l with
  | 0, _ => []
  | _, [] => []
  | n+1, x::xs => x :: list_take_last n xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_supw_time (n : Nat) (days : List Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_supw_time_monotonic (n : Nat) (days : List Nat) (i : Nat) (x : Nat)
  (h1 : n = days.length) (h2 : n ≥ 3) (h3 : i < n) :
  let days' := List.set days i (days[i] + x)
  min_supw_time n days' ≥ min_supw_time n days :=
sorry
-- </vc-theorems>
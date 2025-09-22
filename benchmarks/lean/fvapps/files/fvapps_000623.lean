-- <vc-preamble>
def list_maximum (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | x::xs => xs.foldl Nat.max x

def list_minimum (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | x::xs => xs.foldl Nat.min x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_spaceship_cooldown (n d : Nat) (arrivals : List Nat) : Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem spaceship_cooldown_nonnegative
  (n d : Nat)
  (arrivals : List Nat)
  (h : arrivals.length ≥ 2)
  : solve_spaceship_cooldown n d arrivals ≥ 0 :=
sorry

theorem spaceship_cooldown_upper_bound
  (n d : Nat)
  (arrivals : List Nat)
  (h : arrivals.length ≥ 2)
  : solve_spaceship_cooldown n d arrivals ≤
    ((list_maximum arrivals) - (list_minimum arrivals)).toFloat + d.toFloat :=
sorry

theorem spaceship_cooldown_monotone_delay
  (n d : Nat)
  (arrivals : List Nat)
  (h : arrivals.length ≥ 2)
  : solve_spaceship_cooldown n d arrivals ≤ solve_spaceship_cooldown n (d + 1) arrivals :=
sorry

theorem spaceship_cooldown_known_value1 :
  solve_spaceship_cooldown 3 2 [3, 2, 3] = 1.5 :=
sorry

theorem spaceship_cooldown_known_value2 :
  solve_spaceship_cooldown 2 1 [5, 6] = 2.0 :=
sorry
-- </vc-theorems>
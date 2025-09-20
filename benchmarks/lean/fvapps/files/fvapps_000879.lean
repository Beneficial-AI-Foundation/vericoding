-- <vc-preamble>
def max : List Nat → Nat
| [] => 0
| [x] => x
| (x::xs) => Nat.max x (max xs)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum : List Nat → Nat
| [] => 0
| (x::xs) => x + sum xs

def can_cyborg_escape (n : Nat) (target : Nat) (powers : List Nat) : Bool :=
sorry

def reverse : List Nat → List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem target_less_than_max_always_possible
  (powers : List Nat) (target : Nat) (h1 : powers ≠ []) :
  target ≤ max powers → can_cyborg_escape (powers.length) target powers = true := by
sorry

theorem target_greater_than_sum_impossible
  (powers : List Nat) (extra : Nat) (h1 : powers ≠ []) :
  let target := sum powers + extra + 1
  can_cyborg_escape (powers.length) target powers = false := by
sorry

theorem symmetric_input
  (powers : List Nat) (h1 : powers ≠ []) :
  let target := sum powers / 2
  can_cyborg_escape (powers.length) target powers =
    can_cyborg_escape (powers.length) target (reverse powers) := by
sorry
-- </vc-theorems>
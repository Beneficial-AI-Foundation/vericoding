-- <vc-preamble>
def list_max : List Nat → Nat
| [] => 0
| [x] => x
| (x::xs) => Nat.max x (list_max xs)

def iterate_steps (i j steps : Nat) : Nat × Nat :=
  match steps with
  | 0 => (i, j)
  | n+1 =>
    let (cur_i, cur_j) := iterate_steps i j n
    if cur_i ≤ cur_j then
      (cur_i + cur_j, cur_j)
    else
      (cur_i, cur_j + cur_i)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_min_steps (i j : Nat) (nums : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_min_steps_nonnegative {i j : Nat} {nums : List Nat} :
  find_min_steps i j nums ≥ 0 :=
sorry

theorem find_min_steps_monotonic {i j target : Nat} (hi : i > 1) (hj : j > 1) :
  find_min_steps i j [target] ≤ find_min_steps (i-1) (j-1) [target] :=
sorry
-- </vc-theorems>
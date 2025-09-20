-- <vc-preamble>
def sum_list : List Nat → Nat
  | [] => 0
  | (x::xs) => x + sum_list xs

def select_indices : List Nat → (Nat → Bool) → List Nat
  | [], _ => []
  | (x::xs), f => if f 0 then x::(select_indices xs (fun n => f (n+1)))
                  else select_indices xs (fun n => f (n+1))
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def row_weights (numbers : List Nat) : Nat × Nat := sorry

theorem row_weights_single_element (n : Nat) :
  let (team1, team2) := row_weights [n]
  team2 = 0 ∧ team1 = n := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>
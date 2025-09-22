-- <vc-preamble>
def is_valid_cell_list (cells : List Nat) : Bool :=
  cells.all (fun x => x = 0 ∨ x = 1)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def determine_winner (n : Nat) (cells : List Nat) : String := sorry

def count_max_consecutive_zeros (cells : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem winner_determined_by_max_zeros (n : Nat) (cells : List Nat)
  (h : is_valid_cell_list cells) :
  determine_winner n cells =
    if count_max_consecutive_zeros cells % 2 = 1
    then "Yes"
    else "No" :=
sorry

theorem determine_winner_returns_yes_or_no (n : Nat) (cells : List Nat)
  (h : is_valid_cell_list cells) :
  determine_winner n cells = "Yes" ∨ determine_winner n cells = "No" :=
sorry

theorem all_ones_loses (n : Nat) :
  determine_winner n (List.replicate n 1) = "No" :=
sorry

theorem all_zeros_winner (n : Nat) :
  determine_winner n (List.replicate n 0) =
    if n % 2 = 1
    then "Yes"
    else "No" :=
sorry
-- </vc-theorems>
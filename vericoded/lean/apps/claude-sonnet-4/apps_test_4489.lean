import Mathlib
-- <vc-preamble>
def count_occurrences (cards : List String) (target : String) : Int :=
  match cards with
  | [] => 0
  | head :: tail => 
      if head = target then 1 + count_occurrences tail target
      else count_occurrences tail target
termination_by cards.length

def get_unique_strings (all_strings : List String) : List String :=
  match all_strings with
  | [] => []
  | head :: tail =>
      let rest_unique := get_unique_strings tail
      if head ∈ rest_unique then rest_unique
      else [head] ++ rest_unique
termination_by all_strings.length

def max_net_earnings_helper (unique_blue : List String) (blue_cards : List String) (red_cards : List String) (index : Nat) (current_max : Int) : Int :=
  if index >= unique_blue.length then current_max
  else
    let s := unique_blue[index]!
    let blue_count := count_occurrences blue_cards s
    let red_count := count_occurrences red_cards s
    let net := blue_count - red_count
    let new_max := if net > current_max then net else current_max
    max_net_earnings_helper unique_blue blue_cards red_cards (index + 1) new_max
termination_by unique_blue.length - index

def max_net_earnings (blue_cards : List String) (red_cards : List String) : Int :=
  let unique_blue := get_unique_strings blue_cards
  max_net_earnings_helper unique_blue blue_cards red_cards 0 0

@[reducible, simp]
def solve_precond (blue_cards red_cards : List String) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Lemma showing max_net_earnings_helper preserves lower bound
lemma max_net_earnings_helper_ge_initial (unique_blue : List String) (blue_cards red_cards : List String) 
    (index : Nat) (current_max : Int) :
    max_net_earnings_helper unique_blue blue_cards red_cards index current_max ≥ current_max := by
  unfold max_net_earnings_helper
  split
  · rfl
  · next h =>
    let s := unique_blue[index]!
    let blue_count := count_occurrences blue_cards s
    let red_count := count_occurrences red_cards s
    let net := blue_count - red_count
    let new_max := if net > current_max then net else current_max
    have h_new_max_ge : new_max ≥ current_max := by
      unfold new_max
      split
      · linarith
      · rfl
    have ih := max_net_earnings_helper_ge_initial unique_blue blue_cards red_cards (index + 1) new_max
    exact le_trans h_new_max_ge ih

-- LLM HELPER: Corollary for non-negativity
lemma max_net_earnings_nonneg (blue_cards red_cards : List String) :
    max_net_earnings blue_cards red_cards ≥ 0 := by
  unfold max_net_earnings
  exact max_net_earnings_helper_ge_initial (get_unique_strings blue_cards) blue_cards red_cards 0 0
-- </vc-helpers>

-- <vc-definitions>
def solve (blue_cards red_cards : List String) (h_precond : solve_precond blue_cards red_cards) : Int :=
  max_net_earnings blue_cards red_cards
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (blue_cards red_cards : List String) (result : Int) (h_precond : solve_precond blue_cards red_cards) : Prop :=
  result ≥ 0 ∧ result = max_net_earnings blue_cards red_cards

theorem solve_spec_satisfied (blue_cards red_cards : List String) (h_precond : solve_precond blue_cards red_cards) :
    solve_postcond blue_cards red_cards (solve blue_cards red_cards h_precond) h_precond := by
  unfold solve_postcond solve
  constructor
  · exact max_net_earnings_nonneg blue_cards red_cards
  · rfl
-- </vc-theorems>

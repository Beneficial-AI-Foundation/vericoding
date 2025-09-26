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
-- LLM HELPER
lemma max_net_earnings_helper_preserves_bound (unique_blue blue_cards red_cards : List String) (index : Nat) (init : Int) : 
    max_net_earnings_helper unique_blue blue_cards red_cards index init ≥ init := by
  generalize h_len : unique_blue.length - index = n
  induction n generalizing index init with
  | zero =>
    unfold max_net_earnings_helper
    split
    · simp
    · have : unique_blue.length - index = 0 := h_len
      have : index ≥ unique_blue.length := by omega
      contradiction
  | succ n' ih =>
    unfold max_net_earnings_helper
    split
    · simp
    · next h_cond =>
      let s := unique_blue[index]!
      let blue_count := count_occurrences blue_cards s
      let red_count := count_occurrences red_cards s
      let net := blue_count - red_count
      let new_max := if net > init then net else init
      have h_new_max : new_max ≥ init := by
        unfold new_max
        split
        · next h => exact le_of_lt h
        · simp
      have h_ih : max_net_earnings_helper unique_blue blue_cards red_cards (index + 1) new_max ≥ new_max := by
        apply ih
        omega
      exact le_trans h_new_max h_ih

-- LLM HELPER
lemma max_net_earnings_nonneg (blue_cards red_cards : List String) : 
    max_net_earnings blue_cards red_cards ≥ 0 := by
  unfold max_net_earnings
  exact max_net_earnings_helper_preserves_bound _ _ _ _ _
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

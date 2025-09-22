-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_tweet_clicks (n : Nat) (clicks : List String) : List Nat :=
sorry

def is_valid_click_command (n : Nat) (s : String) : Bool :=
sorry

def get_tweet_count (prev : Nat) (cmd : String) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_length_matches_input {n : Nat} {clicks : List String}
  (h1 : n > 0) (h2 : n ≤ 100) (h3 : clicks.length > 0) :
  (solve_tweet_clicks n clicks).length = clicks.length :=
sorry

theorem counts_are_nonnegative {n : Nat} {clicks : List String}
  (h1 : n > 0) (h2 : n ≤ 100) (h3 : clicks.length > 0) :
  ∀ x ∈ solve_tweet_clicks n clicks, 0 ≤ x ∧ x ≤ n :=
sorry

theorem closeall_resets_to_zero {n : Nat} {clicks : List String}
  (h1 : n > 0) (h2 : n ≤ 100) (h3 : clicks.length > 0) :
  ∀ (i : Nat) (h : i < clicks.length),
  clicks.get ⟨i, h⟩ = "CLOSEALL" →
  (solve_tweet_clicks n clicks).get ⟨i, by rw [output_length_matches_input h1 h2 h3]; exact h⟩ = 0 :=
sorry
-- </vc-theorems>
-- <vc-preamble>
def list_sum : List Nat → Nat
  | [] => 0
  | x::xs => x + list_sum xs

def take_last (n : Nat) (l : List Nat) : List Nat :=
  let rev := l.reverse
  (rev.take n).reverse
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_max_team_score (n : Nat) (ratings : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_max_team_score_upper_bound
  (ratings : List Nat) (h : ratings.length ≥ 3) :
  find_max_team_score ratings.length ratings ≤ list_sum (take_last 3 ratings) :=
sorry

theorem find_max_team_score_lower_bound
  (ratings : List Nat) (h : ratings.length ≥ 3) :
  find_max_team_score ratings.length ratings ≥ list_sum (ratings.take 3) :=
sorry

theorem find_max_team_score_three_elements
  (ratings : List Nat) (h : ratings.length = 3) :
  find_max_team_score ratings.length ratings = list_sum ratings :=
sorry

theorem find_max_team_score_consecutive
  (ratings : List Nat) (h : ratings.length ≥ 3) (i : Nat) (hi : i + 2 < ratings.length) :
  find_max_team_score ratings.length ratings ≥
    ratings[i]! + ratings[i+1]! + ratings[i+2]! :=
sorry

theorem find_max_team_score_wrapping
  (ratings : List Nat) (h : ratings.length ≥ 3) (i : Nat) :
  find_max_team_score ratings.length ratings ≥
    ratings[i % ratings.length]! +
    ratings[(i + 1) % ratings.length]! +
    ratings[(i + 2) % ratings.length]! :=
sorry

theorem find_max_team_score_all_equal
  (n : Nat) (h : n ≥ 3) :
  find_max_team_score n (List.replicate n 1) = 3 :=
sorry
-- </vc-theorems>
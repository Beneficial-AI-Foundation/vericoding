-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rank (names : String) (weights : List Nat) (n : Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem rank_deterministic (names : String) (weights : List Nat) (n : Nat) :
  rank names weights n = rank names weights n :=
  sorry

theorem rank_selects_participant (names : String) (weights : List Nat) (n : Nat) 
  (participants : List String) (h1 : participants.length > 0) 
  (h2 : n ≤ participants.length) :
  (rank names weights n) ∈ participants :=
  sorry

theorem rank_empty_input :
  rank "" [] 1 = "No participants" :=
  sorry

theorem rank_insufficient_participants (name : String) (weight : List Nat) :
  rank name weight 2 = "Not enough participants" :=
  sorry

theorem rank_two_equal_weights (n : String) (m : String) (h : n ≠ m) :
  (rank (n ++ "," ++ m) [1, 1] 1 = n) ∨ 
  (rank (n ++ "," ++ m) [1, 1] 1 = m) :=
  sorry
-- </vc-theorems>
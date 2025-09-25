-- <vc-preamble>
def User.incProgress (self : User) (rank : Rank) : User :=
  sorry

def isValidRank (r : Rank) : Bool :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def getRankProgress (self : User) (rank : Rank) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_rank_input (r : Rank) (u : User) :
  let u' := u.incProgress r
  u'.progress ≥ 0 ∧ isValidRank u'.rank := by
  sorry

theorem invalid_rank_progress (n : Int) (u : User) :
  n ≠ -8 ∧ n ≠ -7 ∧ n ≠ -6 ∧ n ≠ -5 ∧ n ≠ -4 ∧ n ≠ -3 ∧ n ≠ -2 ∧ n ≠ -1 ∧ 
  n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 3 ∧ n ≠ 4 ∧ n ≠ 5 ∧ n ≠ 6 ∧ n ≠ 7 ∧ n ≠ 8 →
  False := by
  sorry

theorem same_rank_progress (r : Rank) (u : User) : 
  u.rank = r →
  let u' := u.incProgress r
  (u'.progress - u.progress) % 100 = 3 ∨ u.rank = Rank.Eight := by
  sorry

theorem one_rank_below_progress (r : Rank) (u : User) :
  r ≠ Rank.Eight →
  let nextRank := Rank.Eight -- simplified for demonstration
  u.rank = nextRank →
  let u' := u.incProgress r
  (u'.progress - u.progress) % 100 = 1 ∨ u'.rank = Rank.Eight := by 
  sorry

theorem max_rank_progress (r : Rank) (u : User) :
  u.rank = Rank.Eight →
  let u' := u.incProgress r
  u'.progress = 0 ∧ u'.rank = Rank.Eight := by
  sorry
-- </vc-theorems>
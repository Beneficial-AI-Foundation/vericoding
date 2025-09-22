-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def update_score (score: List Int) (trump: Int) (alone: Bool) (tricks: List Int) : List Int := sorry

theorem update_score_preserves_length 
  (score: List Int) (trump: Int) (alone: Bool) (tricks: List Int)
  (h1: trump ≥ 1) (h2: trump ≤ 2) 
  (h3: score.length = 2)
  (h4: tricks.length = 5)
  (h5: ∀ t ∈ tricks, t ≥ 1 ∧ t ≤ 2) :
  (update_score score trump alone tricks).length = score.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem update_score_changes_one_team
  (score: List Int) (trump: Int) (alone: Bool) (tricks: List Int)
  (h1: trump ≥ 1) (h2: trump ≤ 2)
  (h3: score.length = 2)
  (h4: tricks.length = 5)
  (h5: ∀ t ∈ tricks, t ≥ 1 ∧ t ≤ 2) :
  let result := update_score score trump alone tricks
  let changed := (List.zip score result).filter (λ p => p.1 ≠ p.2) |>.length
  changed ≤ 1 := sorry

theorem update_score_only_increases
  (score: List Int) (trump: Int) (alone: Bool) (tricks: List Int)
  (h1: trump ≥ 1) (h2: trump ≤ 2)
  (h3: score.length = 2)
  (h4: tricks.length = 5)
  (h5: ∀ t ∈ tricks, t ≥ 1 ∧ t ≤ 2) :
  let result := update_score score trump alone tricks
  let pairs := List.zip score result
  ∀ p ∈ pairs, p.2 ≥ p.1 := sorry

theorem update_score_valid_increments
  (score: List Int) (trump: Int) (alone: Bool) (tricks: List Int)
  (h1: trump ≥ 1) (h2: trump ≤ 2)
  (h3: score.length = 2)
  (h4: tricks.length = 5)
  (h5: ∀ t ∈ tricks, t ≥ 1 ∧ t ≤ 2) :
  let result := update_score score trump alone tricks
  let diffs := (List.zip score result).map (λ p => p.2 - p.1)
  ∀ d ∈ diffs, d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 4 := sorry

theorem update_score_alone_bonus
  (score: List Int) (trump: Int) (alone: Bool) (tricks: List Int)
  (h1: trump ≥ 1) (h2: trump ≤ 2)
  (h3: score.length = 2)
  (h4: tricks.length = 5)
  (h5: ∀ t ∈ tricks, t ≥ 1 ∧ t ≤ 2) :
  let result := update_score score trump alone tricks
  let trump_tricks := tricks.filter (λ t => t = trump) |>.length
  alone ∧ trump_tricks = 5 →
  let diffs := (List.zip score result).map (λ p => p.2 - p.1)
  let max_diff := diffs.foldl max 0
  max_diff = 2 ∨ max_diff = 4 := sorry

theorem update_score_failed_contract
  (score: List Int) (trump: Int) (alone: Bool) (tricks: List Int)
  (h1: trump ≥ 1) (h2: trump ≤ 2)
  (h3: score.length = 2)
  (h4: tricks.length = 5)
  (h5: ∀ t ∈ tricks, t ≥ 1 ∧ t ≤ 2) :
  let result := update_score score trump alone tricks
  let trump_tricks := tricks.filter (λ t => t = trump) |>.length
  trump_tricks ≤ 2 →
  let winning_team := 3 - trump
  ∃ (i : Fin score.length), result.get ⟨i.1, by
    have h := update_score_preserves_length score trump alone tricks h1 h2 h3 h4 h5
    rw [h]
    exact i.2⟩ > score.get i := sorry
-- </vc-theorems>
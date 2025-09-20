-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def strange_coach (players : List String) : String := sorry

theorem strange_coach_sorted
  (players : List String)
  (h : strange_coach players ≠ "forfeit")
  (i j : Nat)
  (hi : i < (strange_coach players).length)
  (hj : j < (strange_coach players).length)
  (hij : i < j) :
  (strange_coach players).data[i] ≤ (strange_coach players).data[j] := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem strange_coach_unique_chars
  (players : List String)
  (h : strange_coach players ≠ "forfeit")
  (i j : Nat)
  (hi : i < (strange_coach players).length)
  (hj : j < (strange_coach players).length)
  (hij : i < j) :
  (strange_coach players).data[i] ≠ (strange_coach players).data[j] := sorry

theorem strange_coach_forfeit_condition
  (players : List String) :
  strange_coach players = "forfeit" ↔
    ∀ c, (players.filter (λ p => p.get 0 = c)).length < 5 := sorry

theorem strange_coach_letter_condition
  (players : List String)
  (h : strange_coach players ≠ "forfeit")
  (c : Char) :
  c ∈ (strange_coach players).toList →
    (players.filter (λ p => p.get 0 = c)).length ≥ 5 := sorry

theorem strange_coach_complete
  (players : List String)
  (h : strange_coach players ≠ "forfeit")
  (c : Char) :
  (players.filter (λ p => p.get 0 = c)).length ≥ 5 →
    c ∈ (strange_coach players).toList := sorry

theorem strange_coach_output_nonempty
  (players : List String)
  (h : players ≠ []) :
  strange_coach players ≠ "" := sorry

theorem strange_coach_output_string
  (players : List String) :
  strange_coach players = "forfeit" ∨
  (∀ c ∈ (strange_coach players).toList, c.isAlpha) := sorry
-- </vc-theorems>
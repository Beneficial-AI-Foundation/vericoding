-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def berserk_rater (synopsis : List String) : String :=
  sorry

def score (s : String) : Int :=
  sorry

def String.hasSubstring (s₁ s₂ : String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem berserk_rater_output_format (synopsis : List String) :
  let result := berserk_rater synopsis
  (result = "worstest episode ever" ∨ result = "bestest episode ever" ∨ String.all result Char.isDigit) :=
sorry

theorem berserk_rater_score_boundaries (synopsis : List String) :
  let result := berserk_rater synopsis
  let score_sum := List.foldl (· + ·) 0 (List.map (fun s => score s.toUpper) synopsis)
  (result = "worstest episode ever" → score_sum < 0) ∧
  (result = "bestest episode ever" → score_sum > 10) ∧
  (result ≠ "worstest episode ever" ∧ result ≠ "bestest episode ever" →
    0 ≤ result.toNat! ∧ result.toNat! ≤ 10) :=
sorry

theorem score_function_output (s : String) :
  let result := score s.toUpper
  (result = 5 ∨ result = -2 ∨ result = -1) ∧
  (s.toUpper.hasSubstring "CLANG" → result = 5) ∧
  (s.toUpper.hasSubstring "CG" → (¬s.toUpper.hasSubstring "CLANG" → result = -2)) ∧
  (¬s.toUpper.hasSubstring "CLANG" ∧ ¬s.toUpper.hasSubstring "CG" → result = -1) :=
sorry

theorem score_precedence_clang_over_cg :
  score "CLANGCG" = 5 ∧ score "CGCLANG" = 5 :=
sorry
-- </vc-theorems>
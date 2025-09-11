-- <vc-preamble>
def berserk_rater (synopsis : List String) : String :=
  sorry

def score (s : String) : Int :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def String.hasSubstring (s₁ s₂ : String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem berserk_rater_output_format (synopsis : List String) :
  let result := berserk_rater synopsis
  (result = "worstest episode ever" ∨ result = "bestest episode ever" ∨ String.all result Char.isDigit) := sorry

theorem berserk_rater_score_boundaries (synopsis : List String) :
  let result := berserk_rater synopsis
  let score_sum := List.foldl (· + ·) 0 (List.map (fun s => score s.toUpper) synopsis)
  (result = "worstest episode ever" → score_sum < 0) ∧
  (result = "bestest episode ever" → score_sum > 10) ∧
  (result ≠ "worstest episode ever" ∧ result ≠ "bestest episode ever" → 
    0 ≤ result.toNat! ∧ result.toNat! ≤ 10) := sorry

theorem score_function_output (s : String) :
  let result := score s.toUpper
  (result = 5 ∨ result = -2 ∨ result = -1) ∧
  (s.toUpper.hasSubstring "CLANG" → result = 5) ∧
  (s.toUpper.hasSubstring "CG" → (¬s.toUpper.hasSubstring "CLANG" → result = -2)) ∧
  (¬s.toUpper.hasSubstring "CLANG" ∧ ¬s.toUpper.hasSubstring "CG" → result = -1) := sorry

theorem score_precedence_clang_over_cg :
  score "CLANGCG" = 5 ∧ score "CGCLANG" = 5 := sorry

/-
info: 'worstest episode ever'
-/
-- #guard_msgs in
-- #eval berserk_rater ["is this the CG from a P2 game?", "Hell, no! Even the CG in the Dreamcast game was more fluid than this!", "Well, at least Gatsu does his clang even against a mere rabbit", "Hey, Cosette was not in this part of the story!", "Ops, everybody dead again! Well, how boring..."]

/-
info: '2'
-/
-- #guard_msgs in
-- #eval berserk_rater ["Farnese unable to shut the fuck up", "awful CG dogs assaulting everybody", "Gatsu clanging the pig apostle!"]

/-
info: 'bestest episode ever'
-/
-- #guard_msgs in
-- #eval berserk_rater ["Holy chain knights being dicks", "Serpico almost getting clanged by Gatsu, but without losing his composure", "lame CG", "Luka getting kicked", "Gatsu going clang against the angels", "Gatsu clanging vs Mozgus, big time!"]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded
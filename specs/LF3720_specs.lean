-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def String.count (s : String) (c : Char) : Nat := sorry
def baby_count (s : String) : Int ⊕ String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem baby_count_result_type (s : String) :
  match baby_count s with
  | Sum.inl n => True 
  | Sum.inr str => str = "Where's the baby?!"
  := sorry

theorem baby_count_matches_formula (s : String) :
  let lowered := s.toLower
  let count_a := lowered.count 'a'
  let count_b := lowered.count 'b' / 2
  let count_y := lowered.count 'y'
  let expected := min count_a (min count_b count_y)
  match baby_count s with
  | Sum.inl n => n = expected ∧ expected > 0
  | Sum.inr _ => expected = 0
  := sorry

theorem baby_count_valid_chars_properties (s : String) :
  let result := baby_count s
  match result with
  | Sum.inl n => 
    n ≥ 0 ∧ 
    s.toLower.count 'a' ≥ n ∧
    s.toLower.count 'b' / 2 ≥ n ∧ 
    s.toLower.count 'y' ≥ n
  | Sum.inr _ => True
  := sorry

theorem baby_count_invalid_chars (s : String) :
  (∀ c ∈ s.data, c ≠ 'a' ∧ c ≠ 'b' ∧ c ≠ 'y') →
  baby_count s = Sum.inr "Where's the baby?!"
  := sorry
-- </vc-theorems>
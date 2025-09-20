-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_textliterals (code : String) : List (Nat × Nat) := sorry

/- Valid result format ensures result is list of natural number pairs -/
-- </vc-definitions>

-- <vc-theorems>
theorem valid_result_format (code : String) :
  ∀ result : List (Nat × Nat), result = get_textliterals code → 
  ∀ p ∈ result, ∃ (s e : Nat), p = (s, e) := sorry

/- All ranges in result are valid positions within code length -/

theorem valid_ranges (code : String) :
  ∀ p ∈ get_textliterals code, 
  let (s, e) := p
  s < e ∧ e ≤ code.length := sorry

/- All result ranges start and end with single quotes -/

theorem valid_quotes (code : String) :
  ∀ p ∈ get_textliterals code,
  let (s, e) := p
  s < code.length ∧ e ≤ code.length →
  code.data[s]! = '\'' ∧ 
  code.data[e - 1]! = '\'' := sorry

/- Result ranges are non-overlapping and ordered -/

theorem non_overlapping (code : String) :
  ∀ i, i < (get_textliterals code).length - 1 →
  let ranges := get_textliterals code
  let p₁ := ranges[i]!
  let p₂ := ranges[i+1]!
  p₁.2 ≤ p₂.1 := sorry

/- Result ranges do not contain SQL comments -/

theorem no_comments (code : String) :
  ∀ p ∈ get_textliterals code,
  let (s, e) := p
  s < code.length ∧ e ≤ code.length →
  ¬ (∃ i, i ≥ s ∧ i + 1 < e ∧
    ((code.data[i]! = '/' ∧ code.data[i+1]! = '*') ∨
     (code.data[i]! = '*' ∧ code.data[i+1]! = '/') ∨
     (code.data[i]! = '-' ∧ code.data[i+1]! = '-'))) := sorry
-- </vc-theorems>
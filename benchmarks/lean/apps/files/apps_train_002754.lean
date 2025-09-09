-- <vc-helpers>
-- </vc-helpers>

def triple_trouble (one two three : String) : String := sorry

theorem triple_trouble_length {one two three : String} :
  one.length = two.length → one.length = three.length →
  (triple_trouble one two three).length = 3 * one.length :=
sorry

theorem triple_trouble_equal_inputs {s : String} {i : Nat} :
  i < s.length →
    let result := triple_trouble s s s;
    ∃ c, s.data.get? i = some c ∧
         result.data.get? (3 * i) = some c ∧
         result.data.get? (3 * i + 1) = some c ∧
         result.data.get? (3 * i + 2) = some c :=
sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
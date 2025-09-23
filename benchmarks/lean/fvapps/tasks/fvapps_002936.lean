-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def dashatize (n : Option Int) : String := sorry

theorem dashatize_basic_props {n : Int} :
  let result := dashatize (some n);
  -- Result is a string containing only digits and dashes
  (∀ c, c ∈ result.data → c = '-' ∨ c.isDigit)
  -- No consecutive dashes - expressed through data list
  ∧ (∀ i, i + 1 < result.data.length → 
      ¬(result.data[i]? = some '-' ∧ result.data[i+1]? = some '-'))
  -- Doesn't start/end with dash
  ∧ (result.length > 0 → result.front ≠ '-')
  ∧ (result.length > 0 → result.back ≠ '-') := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem dashatize_preserves_number {n : Int} :
  let result := dashatize (some n);
  let digits := result.data.filter Char.isDigit;
  String.toNat! (String.mk digits) = Int.natAbs n := sorry

theorem dashatize_none :
  dashatize none = "None" := sorry
-- </vc-theorems>
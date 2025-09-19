-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def kebabize (s : String) : String := sorry

theorem kebabize_contains_only_lowercase_and_hyphens (s : String) : 
  ∀ c, c ∈ (kebabize s).data → c = '-' ∨ (c.toNat ≥ 97 ∧ c.toNat ≤ 122) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem kebabize_no_hyphen_at_bounds (s : String) :
  (kebabize s).length > 0 → 
    (kebabize s).data[0]! ≠ '-' ∧ 
    (kebabize s).data[(kebabize s).length - 1]! ≠ '-' := sorry

theorem kebabize_length_upper_bound (s : String) :
  let num_capitals : Nat := (s.data.filter Char.isUpper).length;
  let num_letters : Nat := (s.data.filter Char.isAlpha).length;
  (kebabize s).length ≤ num_letters + num_capitals := sorry
-- </vc-theorems>
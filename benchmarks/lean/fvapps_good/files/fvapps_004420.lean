-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def alpha_num_inverse (s: String) : String := sorry 

theorem pure_alpha_only_digits {s : String} 
  (h : ∀ c ∈ s.data, c ≥ 'a' ∧ c ≤ 'z') :
  ∀ c ∈ (alpha_num_inverse s).data, c ≥ '0' ∧ c ≤ '9' := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pure_alpha_conversion_correct {s : String}
  (h : ∀ c ∈ s.data, c ≥ 'a' ∧ c ≤ 'z') :
  alpha_num_inverse s = String.join (s.data.map (fun c => toString (c.toNat - 96))) := sorry
-- </vc-theorems>
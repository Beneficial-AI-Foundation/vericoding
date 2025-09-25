-- <vc-preamble>
def string_reverse (s : String) : String :=
  ⟨s.data.reverse⟩
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_string_weight (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem length_weight_relationship {s : String}
  (h : ∀ c ∈ s.data, 'A' ≤ c ∧ c ≤ 'Z') :
  s.length ≤ calculate_string_weight s ∧ calculate_string_weight s ≤ 27 * s.length :=
sorry

theorem invariant_under_reversal {s : String}
  (h : ∀ c ∈ s.data, 'A' ≤ c ∧ c ≤ 'Z') :
  calculate_string_weight s = calculate_string_weight (string_reverse s) :=
sorry

theorem weight_additive {s1 s2 : String}
  (h1 : ∀ c ∈ s1.data, 'A' ≤ c ∧ c ≤ 'Z')
  (h2 : ∀ c ∈ s2.data, 'A' ≤ c ∧ c ≤ 'Z') :
  calculate_string_weight (s1 ++ s2) = calculate_string_weight s1 + calculate_string_weight s2 :=
sorry

theorem a_highest_weight :
  calculate_string_weight "A" > calculate_string_weight "Z" :=
sorry

theorem a_weight_27 :
  calculate_string_weight "A" = 27 :=
sorry

theorem z_weight_2 :
  calculate_string_weight "Z" = 2 :=
sorry
-- </vc-theorems>
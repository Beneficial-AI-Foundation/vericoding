-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def meters (n : Nat) : String := sorry

def Valid_Suffix : List String := ["m", "km", "Mm", "Gm", "Tm", "Pm", "Em", "Zm", "Ym"]
-- </vc-definitions>

-- <vc-theorems>
theorem meters_ends_with_m_suffix (n : Nat) :
  n ≤ 10^24 → ∃ suffix ∈ Valid_Suffix, (meters n).endsWith suffix :=
sorry

theorem meters_starts_with_digit (n : Nat) :
  n ≤ 10^24 → (meters n).get! 0 ∈ ['0','1','2','3','4','5','6','7','8','9'] := 
sorry

theorem meters_numeric_part_less_than_1000 (n : Nat) :
  n ≤ 10^24 → ∃ x : Float, x < 1000 := 
sorry

theorem meters_small_values (n : Nat) :
  1 ≤ n ∧ n ≤ 999 → meters n = s!"{n}m" :=
sorry

theorem meters_kilo_range (n : Nat) :
  1000 ≤ n ∧ n ≤ 999999 → 
  (meters n).endsWith "km" ∧ 
  ∃ x : Float, 1 ≤ x ∧ x < 1000 :=
sorry

theorem meters_special_values :
  meters 1000 = "1km" ∧ 
  meters 1000000 = "1Mm" :=
sorry
-- </vc-theorems>
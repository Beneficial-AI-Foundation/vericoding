-- <vc-preamble>
def TOME : List (String × List Vaccine) :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def vaccine_list (age status month : String) : List Vaccine :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem vaccine_list_ordered (age status month : String) :
  let l := vaccine_list age status month
  ∀ i v₁ v₂, i < l.length - 1 → 
  v₁ = l[i]! → v₂ = l[i+1]! → 
  v₁ ≤ v₂ := by
  sorry

theorem vaccine_list_unique (age status month : String) :
  let l := vaccine_list age status month
  ∀ i j, i < l.length → j < l.length → i ≠ j →
  l[i]! ≠ l[j]! := by
  sorry

theorem vaccine_list_subset_of_valid_vaccines (age status month : String) (v : Vaccine) :
  v ∈ vaccine_list age status month →
  ∃ p : String × List Vaccine, p ∈ TOME ∧ v ∈ p.2 := by
  sorry

theorem vaccine_list_contains_required (age status month : String) :
  ∀ k : String, k ∈ [age, status, month] →
  ∀ p : String × List Vaccine, p ∈ TOME →
  ∀ v : Vaccine, v ∈ p.2 → v ∈ vaccine_list age status month := by
  sorry

theorem vaccine_list_invalid_empty (age status month : String) :
  (∀ p : String × List Vaccine, p ∈ TOME → p.1 ≠ age ∧ p.1 ≠ status ∧ p.1 ≠ month) →
  vaccine_list age status month = [] := by
  sorry
-- </vc-theorems>
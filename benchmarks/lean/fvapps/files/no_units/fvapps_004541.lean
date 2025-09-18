-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countSubstr (s : String) (substr : String) : Nat := sorry

def roast_legacy (workload : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem roast_legacy_score_and_complaints 
  (terms : List String) 
  (fillers : List String)
  (h_terms : ∀ t ∈ terms, t.length > 0)
  (h_fillers : ∀ f ∈ fillers, f.length > 0 ∧ f.length ≤ 10)
  (h_terms_bound : terms.length ≤ 10)
  (h_fillers_bound : fillers.length ≤ 5) :
  let workload := String.intercalate " " (terms ++ fillers)
  let legacy_count := (countSubstr workload.toLower "cobol") * 1000 + 
                     (countSubstr workload.toLower "nonobject") * 500 +
                     (countSubstr workload.toLower "monolithic") * 500 +
                     (countSubstr workload.toLower "fax") * 100 +  
                     (countSubstr workload.toLower "modem") * 100 +
                     (countSubstr workload.toLower "thickclient") * 50 +
                     (countSubstr workload.toLower "tape") * 50 +
                     (countSubstr workload.toLower "floppy") * 50 +
                     (countSubstr workload.toLower "oldschoolit") * 50
  let complaint_count := countSubstr workload.toLower "slow!" +
                        countSubstr workload.toLower "expensive!" +
                        countSubstr workload.toLower "manual!" +
                        countSubstr workload.toLower "down!" +
                        countSubstr workload.toLower "hostage!" +
                        countSubstr workload.toLower "security!"
  let result := roast_legacy workload
  (legacy_count = 0 ∧ complaint_count = 0 → 
    result = "These guys are already DevOps and in the Cloud and the business is happy!") ∧
  (legacy_count ≠ 0 ∨ complaint_count ≠ 0 →
    result = s!"Burn baby burn disco inferno {legacy_count} points earned in this roasting and {complaint_count} complaints resolved!") :=
sorry

theorem roast_legacy_output_type (s : String) :
  let result := roast_legacy s
  result.length > 0 ∧
  (result.startsWith "Burn baby burn" ∨ result.startsWith "These guys") :=
sorry

theorem roast_legacy_case_insensitive (s : String) :
  roast_legacy (s.toLower) = roast_legacy (s.toUpper) :=
sorry
-- </vc-theorems>
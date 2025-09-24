-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def well (ideas : List String) : String := sorry

theorem well_output_valid (ideas : List String) (h : ideas ≠ []) :
  well ideas = "Fail!" ∨ well ideas = "Publish!" ∨ well ideas = "I smell a series!" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem well_case_no_good (ideas : List String) (h1 : ideas ≠ []) 
  (h2 : ∀ x ∈ ideas, x ≠ "good") :
  well ideas = "Fail!" := sorry

theorem well_case_one_or_two_good (ideas : List String) (h : ideas ≠ [])
  (h_count : (ideas.filter (· = "good")).length ≥ 1 ∧ 
             (ideas.filter (· = "good")).length ≤ 2) :
  well ideas = "Publish!" := sorry

theorem well_case_many_good (ideas : List String) (h : ideas ≠ [])
  (h_count : (ideas.filter (· = "good")).length > 2) :
  well ideas = "I smell a series!" := sorry

theorem well_case_sensitive (ideas : List String) (h : ideas ≠ [])
  (h_no_good : "good" ∉ ideas) :
  well ideas = "Fail!" := sorry
-- </vc-theorems>
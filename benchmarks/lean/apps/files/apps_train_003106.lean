-- <vc-helpers>
-- </vc-helpers>

def well (ideas : List String) : String := sorry

theorem well_output_valid (ideas : List String) (h : ideas ≠ []) :
  well ideas = "Fail!" ∨ well ideas = "Publish!" ∨ well ideas = "I smell a series!" := sorry

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

/-
info: 'Fail!'
-/
-- #guard_msgs in
-- #eval well ["bad", "bad", "bad"]

/-
info: 'Publish!'
-/
-- #guard_msgs in
-- #eval well ["good", "bad", "bad", "bad", "bad"]

/-
info: 'I smell a series!'
-/
-- #guard_msgs in
-- #eval well ["good", "bad", "bad", "bad", "bad", "good", "bad", "bad", "good"]

-- Apps difficulty: introductory
-- Assurance level: unguarded
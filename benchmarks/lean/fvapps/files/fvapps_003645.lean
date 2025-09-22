-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def score_test (tests : List Nat) (r w o : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem score_test_properties (tests : List Nat) (r w o : Int)
  (h : ∀ x ∈ tests, x ≤ 2) (h2 : tests.length > 0) :
  score_test tests r w o = 
    (tests.filter (· = 0)).length * r + 
    (tests.filter (· = 1)).length * o - 
    (tests.filter (· = 2)).length * w ∧
  tests.length = (tests.filter (· = 0)).length + 
                 (tests.filter (· = 1)).length + 
                 (tests.filter (· = 2)).length :=
  sorry

theorem all_right_answers (tests : List Nat) (r w o : Int)
  (h : ∀ x ∈ tests, x = 0) :
  score_test tests r w o = tests.length * r :=
  sorry

theorem all_omitted (tests : List Nat) (r w o : Int)
  (h : ∀ x ∈ tests, x = 1) :
  score_test tests r w o = tests.length * o :=
  sorry

theorem all_wrong (tests : List Nat) (r w o : Int)
  (h : ∀ x ∈ tests, x = 2) :
  score_test tests r w o = tests.length * (-w) :=
  sorry
-- </vc-theorems>
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Solution := String

def isSolvable (words : List String) (result : String) : Bool :=
  sorry

def isAlpha (s : String) : Bool :=
  sorry

def isUpper (s : String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_solution_constraints {words : List String} {result : String}
  (h1 : ∀ w ∈ words, isAlpha w ∧ isUpper w)
  (h2 : isAlpha result ∧ isUpper result)
  (h3 : words.length > 0)
  (h4 : ∀ w ∈ words, w.length > 0)
  (h5 : result.length ≥ words.foldr (fun w acc => max w.length acc) 0) :
  ∃ solution : Bool, isSolvable words result = solution :=
sorry

theorem known_valid_cases_work
  (h1 : isSolvable ["SEND", "MORE"] "MONEY" = true)
  (h2 : isSolvable ["SIX", "SEVEN", "SEVEN"] "TWENTY" = true) :
  ∀ words result,
    (words = ["SEND", "MORE"] ∧ result = "MONEY") ∨
    (words = ["SIX", "SEVEN", "SEVEN"] ∧ result = "TWENTY") →
    isSolvable words result = true :=
sorry

theorem modified_valid_case_exists_solution
  {words result : String}
  (h1 : words.length > 0)
  (h2 : result.length > 0)
  (h3 : ∃ (orig_words : List String) (orig_result : String),
        ((orig_words = ["SEND", "MORE"] ∧ orig_result = "MONEY") ∨
         (orig_words = ["SIX", "SEVEN", "SEVEN"] ∧ orig_result = "TWENTY")) ∧
        words.length = orig_result.length) :
  ∃ solution : Bool, isSolvable [words] result = solution :=
sorry
-- </vc-theorems>
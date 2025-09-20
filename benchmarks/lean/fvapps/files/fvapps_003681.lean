-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def translateTableNum (s : String) : String :=
  sorry

def t9_predict (words : List String) (seq : String) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem t9_predict_never_empty (words : List String) (seq : String) :
  seq ≠ "" → ∃ result, t9_predict words seq = result ∧ result.length > 0 :=
sorry

theorem t9_predict_fallback_on_no_matches (words : List String) (seq : String) :
  seq ≠ "" →
  (∀ w ∈ words, translateTableNum w.toLower ≠ seq) →
  ∃ result, t9_predict words seq = [result] ∧ result.length = seq.length :=
sorry

theorem t9_predict_all_matches_sequence (words : List String) (seq : String) :
  seq ≠ "" →
  ∀ w ∈ t9_predict words seq, translateTableNum w.toLower = seq :=
sorry

theorem t9_predict_empty_dict (seq : String) :
  seq ≠ "" →
  ∃ result, t9_predict [] seq = [result] ∧ result.length = seq.length :=
sorry
-- </vc-theorems>
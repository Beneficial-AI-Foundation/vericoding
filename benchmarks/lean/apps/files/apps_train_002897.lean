def textin (s : String) : String :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def containsSubstr (s : String) (sub : String) : Bool :=
  sorry

theorem result_is_string (s : String) :
  textin s = textin s
  := by sorry

theorem output_length_leq_input (s : String) : 
  (textin s).length ≤ s.length 
  := by sorry

theorem no_target_words (s : String) :
  ¬containsSubstr (String.toLower (textin s)) "two" ∧
  ¬containsSubstr (String.toLower (textin s)) "too" ∧
  ¬containsSubstr (String.toLower (textin s)) "to"
  := by sorry

theorem idempotent (s : String) :
  textin (textin s) = textin s 
  := by sorry

-- Apps difficulty: introductory
-- Assurance level: guarded
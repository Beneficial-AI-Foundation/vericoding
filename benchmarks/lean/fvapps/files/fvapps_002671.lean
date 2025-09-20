-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def polybius : String → String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem polybius_output_format (text : String) : 
  (text.data.all (fun c => c.isUpper ∨ c = ' ')) →
  (text.length = (polybius text).length) ∧
  (polybius text).data.all (fun c => c ∈ ['1', '2', '3', '4', '5', ' ']) :=
  sorry

theorem polybius_case_insensitive (text : String) :
  polybius text.toUpper = polybius text.toLower :=
  sorry

theorem polybius_spaces (text : String) :
  text.data.all (fun c => c = ' ') → polybius text = text :=
  sorry

theorem polybius_consistency (text : String) :
  polybius text = polybius text :=
  sorry

theorem polybius_concatenation (text1 text2 : String) :
  polybius (text1 ++ text2) = polybius text1 ++ polybius text2 :=
  sorry
-- </vc-theorems>
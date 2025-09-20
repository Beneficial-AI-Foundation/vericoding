-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def String.findSubstr? (pattern : String) (s : String) : Option String.Pos :=
  sorry

def gym_slang (s : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem gym_slang_length (s : String) :
  String.length (gym_slang s) ≤ String.length s :=
sorry

theorem gym_slang_case_preserving_prob (s : String) :
  (String.findSubstr? "Probably" s).isSome → (String.findSubstr? "Prolly" (gym_slang s)).isSome :=
sorry

theorem gym_slang_case_preserving_prob_lower (s : String) :
  (String.findSubstr? "probably" s).isSome → (String.findSubstr? "prolly" (gym_slang s)).isSome :=
sorry

theorem gym_slang_all_transformations (s : String) :
  let sLower := s.toLower
  let resultLower := (gym_slang s).toLower
  (Option.isSome (String.findSubstr? "probably" sLower) ↔ Option.isSome (String.findSubstr? "prolly" resultLower)) ∧
  (Option.isSome (String.findSubstr? "combination" sLower) ↔ Option.isSome (String.findSubstr? "combo" resultLower)) :=
sorry

theorem gym_slang_identity (s : String) :
  (Option.isNone (String.findSubstr? "probably" s.toLower)) →
  (Option.isNone (String.findSubstr? "i am" s.toLower)) →
  (Option.isNone (String.findSubstr? "instagram" s.toLower)) →
  (Option.isNone (String.findSubstr? "do not" s.toLower)) →
  (Option.isNone (String.findSubstr? "going to" s.toLower)) →
  (Option.isNone (String.findSubstr? "combination" s.toLower)) →
  gym_slang s = s :=
sorry
-- </vc-theorems>
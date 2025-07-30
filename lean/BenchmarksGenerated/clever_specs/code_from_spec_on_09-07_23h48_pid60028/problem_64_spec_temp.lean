def problem_spec
-- function signature
(implementation: String → Nat)
-- inputs
(string: String) :=
let isVowel (c : Char) :=
  let vowels := "aeiouAEIOU"
  vowels.contains c
let isY (c : Char) := c = 'y' ∨ c = 'Y'
-- spec
let spec (result: Nat) :=
string.data.all (fun c => c.isAlpha) →
if string.length = 1 then
  result = if isVowel string.data[0]! ∨ isY string.data[0]! then 1 else 0
else
  result = (if isVowel string.data[0]! then 1 else 0) + implementation (string.drop 1)
-- program termination
∃ result, implementation string = result ∧
spec result

-- LLM HELPER
lemma string_drop_length_lt (s : String) (h : s.length > 0) : (s.drop 1).length < s.length := by
  have : s.drop 1 = s.data.drop 1 |>.asString := by simp [String.drop]
  have : (s.drop 1).length = (s.data.drop 1).length := by simp [String.length]
  rw [this]
  simp [List.length_drop]
  omega

-- LLM HELPER
def countVowelsAndY (s: String) : Nat :=
  if h : s.length = 0 then 0
  else
    let c := s.data[0]!
    let isVowel (c : Char) :=
      let vowels := "aeiouAEIOU"
      vowels.contains c
    let isY (c : Char) := c = 'y' ∨ c = 'Y'
    let count := if isVowel c ∨ isY c then 1 else 0
    count + countVowelsAndY (s.drop 1)
termination_by s.length
decreasing_by 
  simp_wf
  apply string_drop_length_lt
  omega

def implementation (string: String) : Nat := countVowelsAndY string

-- LLM HELPER
lemma countVowelsAndY_length_one (s: String) :
  s.length = 1 →
  let isVowel (c : Char) :=
    let vowels := "aeiouAEIOU"
    vowels.contains c
  let isY (c : Char) := c = 'y' ∨ c = 'Y'
  countVowelsAndY s = if isVowel s.data[0]! ∨ isY s.data[0]! then 1 else 0 := by
  intro h
  simp [countVowelsAndY, h]
  have : (s.drop 1).length = 0 := by
    have : (s.drop 1).length = (s.data.drop 1).length := by simp [String.length, String.drop]
    rw [this]
    simp [List.length_drop]
    omega
  simp [this, countVowelsAndY]

-- LLM HELPER
lemma countVowelsAndY_length_gt_one (s: String) :
  s.length > 1 →
  let isVowel (c : Char) :=
    let vowels := "aeiouAEIOU"
    vowels.contains c
  let isY (c : Char) := c = 'y' ∨ c = 'Y'
  countVowelsAndY s = (if isVowel s.data[0]! then 1 else 0) + countVowelsAndY (s.drop 1) := by
  intro h
  simp [countVowelsAndY]
  have : ¬s.length = 0 := by omega
  simp [this]
  by_cases hv : "aeiouAEIOU".contains s.data[0]!
  · simp [hv]
    ring
  · simp [hv]
    by_cases hy : s.data[0]! = 'y' ∨ s.data[0]! = 'Y'
    · simp [hy]
      ring
    · simp [hy]

theorem correctness
(s: String)
: problem_spec implementation s := by
  simp [problem_spec, implementation]
  use countVowelsAndY s
  constructor
  · rfl
  · intro h
    split
    · apply countVowelsAndY_length_one
      assumption
    · apply countVowelsAndY_length_gt_one
      omega
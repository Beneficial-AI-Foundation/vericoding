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
  result = (if isVowel string.data[0]! then 1 else 0) + implementation (string.drop 1);
-- program termination
∃ result, implementation string = result ∧
spec result

-- LLM HELPER
def countVowelsAndY (s: String) : Nat :=
  if s.length = 0 then 0
  else
    let c := s.data[0]!
    let isVowel (c : Char) :=
      let vowels := "aeiouAEIOU"
      vowels.contains c
    let isY (c : Char) := c = 'y' ∨ c = 'Y'
    let count := if isVowel c ∨ isY c then 1 else 0
    count + countVowelsAndY (s.drop 1)

def implementation (string: String) : Nat := countVowelsAndY string

-- LLM HELPER
lemma countVowelsAndY_spec (s: String) : 
  let isVowel (c : Char) :=
    let vowels := "aeiouAEIOU"
    vowels.contains c
  let isY (c : Char) := c = 'y' ∨ c = 'Y'
  s.data.all (fun c => c.isAlpha) →
  if s.length = 1 then
    countVowelsAndY s = if isVowel s.data[0]! ∨ isY s.data[0]! then 1 else 0
  else if s.length = 0 then
    countVowelsAndY s = 0
  else
    countVowelsAndY s = (if isVowel s.data[0]! then 1 else 0) + countVowelsAndY (s.drop 1) := by
  intro h
  simp [countVowelsAndY]
  split
  · simp
  · split
    · simp
    · simp

-- LLM HELPER
lemma countVowelsAndY_recursive (s: String) :
  let isVowel (c : Char) :=
    let vowels := "aeiouAEIOU"
    vowels.contains c
  let isY (c : Char) := c = 'y' ∨ c = 'Y'
  s.length > 0 →
  countVowelsAndY s = (if isVowel s.data[0]! ∨ isY s.data[0]! then 1 else 0) + countVowelsAndY (s.drop 1) := by
  intro h
  simp [countVowelsAndY]
  split
  · contradiction
  · simp
    split <;> simp

theorem correctness
(s: String)
: problem_spec implementation s := by
  simp [problem_spec, implementation]
  use countVowelsAndY s
  constructor
  · rfl
  · intro h
    split
    · simp [countVowelsAndY_spec]
      apply countVowelsAndY_spec
      exact h
    · simp [countVowelsAndY_recursive]
      apply countVowelsAndY_recursive
      omega
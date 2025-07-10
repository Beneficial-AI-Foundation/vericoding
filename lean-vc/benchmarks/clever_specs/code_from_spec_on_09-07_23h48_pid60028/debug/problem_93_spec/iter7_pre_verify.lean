def problem_spec
-- function signature
(implementation: String → String)
-- inputs
(s: String) :=
-- spec
let spec (result : String) :=
  s.data.all (λ c => c.isAlpha) →
  result.length = s.length ∧
  (∀ i, i < s.length →
    let c := s.data[i]!;
    let c' := result.data[i]!;
    match c with
    | 'a' | 'e' | 'i' | 'o' | 'u' | 'A' | 'E' | 'I' | 'O' | 'U' =>
      c.isUpper → c'.val = c.toLower.val.toNat + 2 ∧
      c.isLower → c'.val = c.toUpper.val.toNat + 2
    | _ =>
      c.isUpper → c' = c.toLower ∧
      c.isLower → c' = c.toUpper)
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- LLM HELPER
def isVowel (c: Char) : Bool :=
  c = 'a' || c = 'e' || c = 'i' || c = 'o' || c = 'u' ||
  c = 'A' || c = 'E' || c = 'I' || c = 'O' || c = 'U'

-- LLM HELPER
def transformChar (c: Char) : Char :=
  if isVowel c then
    if c.isUpper then
      Char.ofNat (c.toLower.val.toNat + 2)
    else
      Char.ofNat (c.toUpper.val.toNat + 2)
  else
    if c.isUpper then
      c.toLower
    else
      c.toUpper

def implementation (s: String) : String :=
  String.mk (s.data.map transformChar)

-- LLM HELPER
lemma string_length_map (s: String) : (String.mk (s.data.map transformChar)).length = s.length := by
  simp [String.length, String.mk]

-- LLM HELPER
lemma string_data_get_map (s: String) (i: Nat) (h: i < s.length) :
  (String.mk (s.data.map transformChar)).data[i]! = transformChar (s.data[i]!) := by
  simp [String.mk, List.getElem!]
  rw [List.getElem!_map]

-- LLM HELPER
lemma isVowel_match (c: Char) :
  (match c with
   | 'a' | 'e' | 'i' | 'o' | 'u' | 'A' | 'E' | 'I' | 'O' | 'U' => true
   | _ => false) = isVowel c := by
  cases c using Char.cases
  simp [isVowel]
  split <;> simp_all

-- LLM HELPER
lemma transformChar_spec (c: Char) :
  match c with
  | 'a' | 'e' | 'i' | 'o' | 'u' | 'A' | 'E' | 'I' | 'O' | 'U' =>
    c.isUpper → (transformChar c).val = c.toLower.val.toNat + 2 ∧
    c.isLower → (transformChar c).val = c.toUpper.val.toNat + 2
  | _ =>
    c.isUpper → transformChar c = c.toLower ∧
    c.isLower → transformChar c = c.toUpper := by
  simp [transformChar]
  rw [← isVowel_match]
  split
  · simp [isVowel]
    split <;> simp [Char.ofNat_val]
  · simp [isVowel]
    split <;> simp

theorem correctness
(s: String)
: problem_spec implementation s := by
  simp [problem_spec, implementation]
  use String.mk (s.data.map transformChar)
  constructor
  · rfl
  · intro h
    constructor
    · exact string_length_map s
    · intro i hi
      rw [string_data_get_map s i hi]
      exact transformChar_spec (s.data[i]!)
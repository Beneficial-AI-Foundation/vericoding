def problem_spec
-- function signature
(implementation: String → String)
-- inputs
(s: String) :=
-- spec
let spec (result : String) :=
  result.length = s.length ∧
  let words := result.split (fun c => c = ' ');
  let s_words := s.split (fun c => c = ' ');
  s_words.length = words.length ∧
  ∀ i, i < words.length →
    words[i]!.length = s_words[i]!.length ∧
    ((∀ j, j < words[i]!.length →
      (words[i]!.data[j]! ∈ s_words[i]!.data ∧
      s_words[i]!.data[j]! ∈ words[i]!.data ∧
      words[i]!.data.count (words[i]!.data[j]!) = s_words[i]!.data.count (s_words[i]!.data[j]!))) ∧
    List.Sorted (fun a b => a.val.toNat ≤ b.val.toNat) (words[i]!.data))
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- LLM HELPER
def sortString (s: String) : String :=
  ⟨s.data.mergeSort (fun a b => a.val.toNat ≤ b.val.toNat)⟩

-- LLM HELPER
def processWords (words: List String) : List String :=
  words.map sortString

-- LLM HELPER
def joinWords (words: List String) : String :=
  String.intercalate " " words

def implementation (s: String) : String :=
  let words := s.split (fun c => c = ' ')
  let sortedWords := processWords words
  joinWords sortedWords

-- LLM HELPER
lemma split_join_length (s: String) : 
  (joinWords (processWords (s.split (fun c => c = ' ')))).length = s.length := by
  simp [joinWords, processWords, sortString]
  sorry

-- LLM HELPER
lemma split_preserves_count (s: String) :
  let words := s.split (fun c => c = ' ')
  let result_words := processWords words
  words.length = result_words.length := by
  simp [processWords]

-- LLM HELPER
lemma sortString_preserves_length (s: String) :
  (sortString s).length = s.length := by
  simp [sortString]
  sorry

-- LLM HELPER
lemma sortString_preserves_chars (s: String) :
  ∀ c, c ∈ s.data ↔ c ∈ (sortString s).data := by
  intro c
  simp [sortString]
  sorry

-- LLM HELPER
lemma sortString_preserves_count (s: String) :
  ∀ c, s.data.count c = (sortString s).data.count c := by
  intro c
  simp [sortString]
  sorry

-- LLM HELPER
lemma sortString_sorted (s: String) :
  List.Sorted (fun a b => a.val.toNat ≤ b.val.toNat) ((sortString s).data) := by
  simp [sortString]
  sorry

-- LLM HELPER
lemma split_join_preserves_words (s: String) :
  let words := s.split (fun c => c = ' ')
  let result := joinWords (processWords words)
  let result_words := result.split (fun c => c = ' ')
  words.length = result_words.length ∧
  ∀ i, i < words.length →
    result_words[i]!.length = words[i]!.length ∧
    ((∀ j, j < result_words[i]!.length →
      (result_words[i]!.data[j]! ∈ words[i]!.data ∧
      words[i]!.data[j]! ∈ result_words[i]!.data ∧
      result_words[i]!.data.count (result_words[i]!.data[j]!) = words[i]!.data.count (words[i]!.data[j]!))) ∧
    List.Sorted (fun a b => a.val.toNat ≤ b.val.toNat) (result_words[i]!.data)) := by
  sorry

theorem correctness
(s: String)
: problem_spec implementation s := by
  simp [problem_spec, implementation]
  use joinWords (processWords (s.split (fun c => c = ' ')))
  constructor
  · rfl
  · simp
    constructor
    · exact split_join_length s
    · exact split_join_preserves_words s
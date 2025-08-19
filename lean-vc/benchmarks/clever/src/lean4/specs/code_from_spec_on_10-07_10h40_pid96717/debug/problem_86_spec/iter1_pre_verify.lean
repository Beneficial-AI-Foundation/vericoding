import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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
    List.Sorted Nat.le (words[i]!.data.map (fun c => c.val.toNat)))
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- LLM HELPER
def sortStringChars (s: String) : String :=
  String.mk (s.data.mergeSort (fun c1 c2 => c1.val.toNat ≤ c2.val.toNat))

-- LLM HELPER
def sortWord (word: String) : String :=
  sortStringChars word

-- LLM HELPER
def processWords (words: List String) : List String :=
  words.map sortWord

-- LLM HELPER
def joinWords (words: List String) : String :=
  match words with
  | [] => ""
  | [w] => w
  | w :: ws => w ++ " " ++ joinWords ws

def implementation (s: String) : String := 
  let words := s.split (fun c => c = ' ')
  let sortedWords := processWords words
  joinWords sortedWords

-- LLM HELPER
lemma sortStringChars_length (s: String) : (sortStringChars s).length = s.length := by
  unfold sortStringChars
  simp [String.length_mk, List.length_mergeSort]

-- LLM HELPER
lemma sortStringChars_data_perm (s: String) : 
  (sortStringChars s).data ~ s.data := by
  unfold sortStringChars
  simp [String.mk_data, List.perm_mergeSort]

-- LLM HELPER
lemma sortStringChars_sorted (s: String) : 
  List.Sorted Nat.le ((sortStringChars s).data.map (fun c => c.val.toNat)) := by
  unfold sortStringChars
  simp [String.mk_data]
  apply List.Sorted.map
  apply List.sorted_mergeSort

-- LLM HELPER
lemma processWords_length (words: List String) : 
  (processWords words).length = words.length := by
  unfold processWords
  simp [List.length_map]

-- LLM HELPER
lemma processWords_nth (words: List String) (i: Nat) (h: i < words.length) :
  (processWords words)[i]! = sortWord words[i]! := by
  unfold processWords
  simp [List.getElem_map]

-- LLM HELPER
lemma joinWords_split_length (words: List String) :
  (joinWords words).split (fun c => c = ' ') = words := by
  sorry

-- LLM HELPER
lemma joinWords_length (words: List String) :
  (joinWords words).length = words.foldl (fun acc w => acc + w.length) 0 + (words.length - 1) := by
  sorry

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  unfold problem_spec
  use implementation s
  constructor
  · rfl
  · unfold implementation
    let words := s.split (fun c => c = ' ')
    let sortedWords := processWords words
    let result := joinWords sortedWords
    constructor
    · sorry -- length equality
    · constructor
      · sorry -- word count equality
      · intro i hi
        constructor
        · sorry -- word length equality
        · constructor
          · sorry -- character membership and counts
          · sorry -- sorted property
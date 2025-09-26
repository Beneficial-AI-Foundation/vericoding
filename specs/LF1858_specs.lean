-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def spellchecker (wordlist : List String) (queries : List String) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem spellchecker_output_length 
  (wordlist : List String) (queries : List String) :
  List.length (spellchecker wordlist queries) = List.length queries :=
sorry

theorem spellchecker_result_in_wordlist
  (wordlist : List String) (queries : List String) :
  ∀ r ∈ spellchecker wordlist queries, r = "" ∨ r ∈ wordlist :=
sorry

theorem spellchecker_exact_match
  (wordlist : List String) (queries : List String) :
  ∀ (q : String), q ∈ queries → q ∈ wordlist → 
  List.get! (spellchecker wordlist queries) (List.indexOf q queries) = q :=
sorry

theorem spellchecker_case_insensitive
  (wordlist : List String) (queries : List String) :
  ∀ (q : String) (r : String),
  q ∈ queries →
  r = List.get! (spellchecker wordlist queries) (List.indexOf q queries) →
  r ≠ "" →
  String.toLower r = String.toLower q →
  r ∈ wordlist :=
sorry

theorem spellchecker_self_query
  (wordlist : List String) :
  spellchecker wordlist wordlist = wordlist :=
sorry

theorem spellchecker_vowel_patterns
  (wordlist : List String) (queries : List String) :
  ∀ (q : String) (r : String),
  q ∈ queries →
  r = List.get! (spellchecker wordlist queries) (List.indexOf q queries) →
  r ≠ "" →
  let q_pattern := (String.toLower q).replace "a" "_"
                    |>.replace "e" "_"
                    |>.replace "i" "_"
                    |>.replace "o" "_"
                    |>.replace "u" "_"
  let r_pattern := (String.toLower r).replace "a" "_"
                    |>.replace "e" "_"
                    |>.replace "i" "_"
                    |>.replace "o" "_"
                    |>.replace "u" "_"
  q_pattern = r_pattern →
  r ∈ wordlist :=
sorry
-- </vc-theorems>
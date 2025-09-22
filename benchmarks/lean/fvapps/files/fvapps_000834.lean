-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def make_word_label (word : String) (label : String) : String := sorry

def solve_spam_dataset (cases : List (List String)) : List Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem case_counts_match_n (ns : List Nat) :
  ns.all (λ n => n > 0 ∧ n ≤ 10) →
  let cases := ns.map (λ n => (toString n) :: List.replicate n (make_word_label "word" "0")) 
  let results := solve_spam_dataset cases
  results.length = cases.length := sorry 

theorem arbitrary_words_and_labels 
  (test_data : List (Nat × List String × List String)) :
  test_data.all (λ (n, words, labels) => 
    n > 0 ∧ n ≤ 10 ∧ 
    words.length > 0 ∧ words.length ≤ 5 ∧
    labels.all (λ l => l = "0" ∨ l = "1") ∧
    labels.length > 0 ∧ labels.length ≤ 5) →
  let cases := test_data.map (λ (n, words, labels) =>
    (toString n) :: (List.zip words labels).map (λ (w,l) => make_word_label w l))
  let results := solve_spam_dataset cases
  results.length = cases.length ∧
  results.all (λ x => x ≥ 0) := sorry

theorem single_word_multiple_labels
  (test_data : List (Nat × String × List String)) :
  test_data.all (λ (n, word, labels) =>
    n > 0 ∧ n ≤ 10 ∧
    word.length > 0 ∧
    labels.all (λ l => l = "0" ∨ l = "1") ∧ 
    labels.length > 0 ∧ labels.length ≤ 10) →
  let cases := test_data.map (λ (n, word, labels) =>
    (toString n) :: labels.map (λ l => make_word_label word l))
  let results := solve_spam_dataset cases
  results.length = cases.length ∧
  (List.zipWith (λ result (n, _, labels) => result ≤ labels.length) results test_data).all id := sorry
-- </vc-theorems>
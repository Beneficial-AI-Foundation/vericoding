-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_rhyming_words (test_cases : List (List String)) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_format_prop {test_cases : List (List String)}
  (h1 : ∀ case ∈ test_cases, case.length > 0)
  (h2 : test_cases.length > 0) :
  let result := find_rhyming_words test_cases
  result.head? = some "Case : 1" ∧ 
  (result.filter (fun line => line.startsWith "Case :")).length = test_cases.length :=
sorry

theorem words_preserved_prop {test_cases : List (List String)} 
  (h1 : ∀ case ∈ test_cases, case.length > 0)
  (h2 : test_cases.length > 0) :
  let result := find_rhyming_words test_cases
  let input_words := test_cases.join
  let output_words := (result.filter (fun line => ¬line.startsWith "Case :")).bind (fun s => (s.split (. = ' ')))
  List.all input_words (fun w => w ∈ output_words) ∧
  List.all output_words (fun w => w ∈ input_words) :=
sorry

theorem rhyming_words_grouped_prop {test_cases : List (List String)}
  (h1 : ∀ case ∈ test_cases, case.length ≥ 2)
  (h2 : test_cases.length > 0) :
  let result := find_rhyming_words test_cases
  ∀ line ∈ result, ¬line.startsWith "Case :" →
    let words := line.split (. = ' ')
    words.length > 1 →
    let suffix := (words.head?.getD "").takeRight 3
    (∀ w ∈ words, w.takeRight 3 = suffix) ∧
    ∀ x ∈ words, ∀ y ∈ words, x ≤ y ∨ y ≤ x :=
sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval find_rhyming_words [["nope", "qwerty", "hope"]]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval find_rhyming_words [["brain", "drain", "request", "grain", "nest"]]

/-
info: expected3
-/
-- #guard_msgs in
-- #eval find_rhyming_words [["these", "words", "dont", "rhyme"]]
-- </vc-theorems>
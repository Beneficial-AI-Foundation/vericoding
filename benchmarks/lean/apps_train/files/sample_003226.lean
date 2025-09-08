/-
Your task is to remove all duplicate words from a string, leaving only single (first) words entries.

Example:

Input:

'alpha beta beta gamma gamma gamma delta alpha beta beta gamma gamma gamma delta'

Output:

'alpha beta gamma delta'
-/

-- <vc-helpers>
-- </vc-helpers>

def removeDuplicateWords (s : String) : String := sorry

/- The output of removeDuplicateWords contains no duplicate words -/

theorem no_duplicates {s : String} :
  let result := removeDuplicateWords s
  let resultWords := (result.splitOn " ")
  List.Nodup resultWords := by sorry

/- Words in the output appear in the same order as their first occurrence in the input -/

theorem preserves_order {s : String} :
  let inputWords := (s.splitOn " ")
  let outputWords := (removeDuplicateWords s).splitOn " " 
  ∀ w ∈ outputWords, 
    List.indexOf w inputWords = List.indexOf w inputWords := by sorry

/- All words in the output appear in the input -/

theorem output_subset_input {s : String} :
  let inputWords := (s.splitOn " ")
  let outputWords := (removeDuplicateWords s).splitOn " "
  ∀ w ∈ outputWords, w ∈ inputWords := by sorry

/-
info: 'alpha beta gamma delta'
-/
-- #guard_msgs in
-- #eval remove_duplicate_words "alpha beta beta gamma gamma gamma delta alpha beta beta gamma gamma gamma delta"

/-
info: 'my cat is fat'
-/
-- #guard_msgs in
-- #eval remove_duplicate_words test2

-- Apps difficulty: introductory
-- Assurance level: unguarded
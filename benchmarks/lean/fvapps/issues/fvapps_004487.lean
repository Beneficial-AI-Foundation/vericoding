-- <vc-preamble>
def isLower (c : Char) : Bool := sorry
def isUpper (c : Char) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pseudo_sort (s : String) : String := sorry

theorem pseudo_sort_preserves_words {word_list : List String} (h : word_list ≠ []) :
  let sentence := String.intercalate " " word_list
  let result := pseudo_sort sentence
  let orig_words := word_list.filter (λ w => w.trim ≠ "")
  let result_words := (result.split (· = ' ')).filter (λ w => w.trim ≠ "")
  ∀ w, w ∈ orig_words ↔ w ∈ result_words := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pseudo_sort_ordering {word_list : List String} (h : word_list ≠ []) :
  let sentence := String.intercalate " " word_list
  let result := (pseudo_sort sentence).split (· = ' ')
  let lowercase := result.filter (λ w => !w.isEmpty ∧ isLower (w.front))
  let uppercase := result.filter (λ w => !w.isEmpty ∧ isUpper (w.front))
  (∀ x y, x ∈ lowercase → y ∈ lowercase → x.data < y.data → result.indexOf x < result.indexOf y) ∧ 
  (∀ x y, x ∈ uppercase → y ∈ uppercase → x.data < y.data → result.indexOf x > result.indexOf y) ∧
  (∀ l u, l ∈ lowercase → u ∈ uppercase → result.indexOf l < result.indexOf u) := sorry

theorem pseudo_sort_handles_punctuation (text : String) :
  let result := pseudo_sort text
  ∀ c, c ∈ "!\"#$%&'()*+,-./:;<=>?@[\\]^_`{|}~".data → 
    ¬(c ∈ result.data) := sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval pseudo_sort "Land of the Old Thirteen! Massachusetts land! land of Vermont and Connecticut!"

/-
info: expected2
-/
-- #guard_msgs in
-- #eval pseudo_sort "I, habitan of the Alleghanies, treating of him as he is in himself in his own rights"

/-
info: expected3
-/
-- #guard_msgs in
-- #eval pseudo_sort "And I send these words to Paris with my love"
-- </vc-theorems>
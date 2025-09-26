-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isAnagram (s1 s2 : String) : Bool := sorry

def grabscrab (said : String) (possibleWords : List String) : List String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem grabscrab_words_in_list (said : String) (possibleWords : List String) :
  ∀ w ∈ grabscrab said possibleWords, w ∈ possibleWords := sorry

theorem grabscrab_words_are_anagrams (said : String) (possibleWords : List String) :
  ∀ w ∈ grabscrab said possibleWords, isAnagram w said = true := sorry

theorem grabscrab_contains_all_anagrams (said : String) (possibleWords : List String) :
  ∀ w ∈ possibleWords, isAnagram w said = true → w ∈ grabscrab said possibleWords := sorry

theorem grabscrab_preserves_order (said : String) (possibleWords : List String) :
  ∀ (i j : Nat), i < j →
    let result := grabscrab said possibleWords
    ∀ (wi wj : String), 
      wi ∈ result → wj ∈ result →
      List.indexOf wi possibleWords < List.indexOf wj possibleWords → 
      List.indexOf wi result < List.indexOf wj result := sorry

theorem grabscrab_empty_list (said : String) :
  grabscrab said [] = [] := sorry

theorem grabscrab_result_unique (said : String) (possibleWords : List String) :
  let result := grabscrab said possibleWords
  result.length = (result.eraseDups).length := sorry

/-
info: ['first']
-/
-- #guard_msgs in
-- #eval grabscrab "trisf" ["first"]

/-
info: ['sport', 'ports']
-/
-- #guard_msgs in
-- #eval grabscrab "ortsp" ["sport", "parrot", "ports", "matey"]

/-
info: []
-/
-- #guard_msgs in
-- #eval grabscrab "ourf" ["one", "two", "three"]
-- </vc-theorems>
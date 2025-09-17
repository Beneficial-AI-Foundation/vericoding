-- <vc-preamble>
def is_prefix_of_word (sentence search : String) : Int :=
  sorry

def startsWith (s₁ s₂ : String) : Bool :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def words (s : String) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_search_property {sentence : String} :
  is_prefix_of_word sentence "" = 1 :=
  sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval is_prefix_of_word "i love eating burger" "burg"

/-
info: 2
-/
-- #guard_msgs in
-- #eval is_prefix_of_word "this problem is an easy problem" "pro"

/-
info: -1
-/
-- #guard_msgs in
-- #eval is_prefix_of_word "i am tired" "you"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
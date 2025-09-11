-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mutations (alice : List String) (bob : List String) (word : String) (first : Nat) : Nat := sorry

def hasOnlyUniqueLetters (s : String) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mutations_result_binary (alice : List String) (bob : List String) (word : String) (first : Nat) :
  mutations alice bob word first = 0 ∨ mutations alice bob word first = 1 := sorry

theorem mutations_no_valid_moves (alice : List String) (bob : List String) (word : String) (first : Nat) :
  (¬∃ w ∈ alice, hasOnlyUniqueLetters w) → 
  (¬∃ w ∈ bob, hasOnlyUniqueLetters w) →
  mutations alice bob word first ≠ first := sorry

theorem mutations_equal_lists_terminates (alice bob : List String) (h1 : alice.length = bob.length) (h2 : alice.length ≥ 10) :
  alice ≠ [] →
  let firstWord := alice[0]
  mutations alice bob firstWord 0 = 0 ∨ mutations alice bob firstWord 0 = 1 := sorry

theorem mutations_empty_lists (word : String) :
  mutations [] [] word 0 = 0 ∨ mutations [] [] word 0 = 1 := sorry

theorem mutations_single_item_lists :
  mutations ["pest"] ["best"] "test" 0 = 0 ∨ mutations ["pest"] ["best"] "test" 0 = 1 := sorry

theorem mutations_same_words :
  mutations (List.replicate 5 "test") (List.replicate 5 "test") "test" 0 = 0 ∨ 
  mutations (List.replicate 5 "test") (List.replicate 5 "test") "test" 0 = 1 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval mutations ["plat", "rend", "bear", "soar", "mare", "pare", "flap", "neat", "clan", "pore"] ["boar", "clap", "farm", "lend", "near", "peat", "pure", "more", "plan", "soap"] "send" 0

/-
info: 0
-/
-- #guard_msgs in
-- #eval mutations alice bob "flip" 1

/-
info: 0
-/
-- #guard_msgs in
-- #eval mutations alice bob "maze" 0
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded
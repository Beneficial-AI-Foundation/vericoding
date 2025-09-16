-- <vc-preamble>
def common_ground (s1 s2 : String) : String :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def split (s : String) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem common_ground_subset (s1 s2 : String) :
  let result := common_ground s1 s2
  result ≠ "death" →
  (∀ w, w ∈ split result → 
    w ∈ split s1 ∧ w ∈ split s2) :=
sorry

theorem common_ground_order (s1 s2 : String) :
  let result := common_ground s1 s2
  result ≠ "death" →
  ∀ i j, i < j → i < (split result).length → j < (split result).length →
    let s2_words := split s2
    let result_words := split result
    s2_words.findIdx (· = result_words[i]!) < 
    s2_words.findIdx (· = result_words[j]!) :=
sorry

theorem common_ground_no_overlap (s1 s2 : String) :
  (∀ w1 w2, w1 ∈ split s1 → w2 ∈ split s2 → w1 ≠ w2) →
  common_ground s1 s2 = "death" :=
sorry

/-
info: 'eat chicken'
-/
-- #guard_msgs in
-- #eval common_ground "eat chicken" "eat chicken and rice"

/-
info: 'drink a coke'
-/
-- #guard_msgs in
-- #eval common_ground "eat a burger and drink a coke" "drink a coke"

/-
info: 'death'
-/
-- #guard_msgs in
-- #eval common_ground "i like turtles" "what are you talking about"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded
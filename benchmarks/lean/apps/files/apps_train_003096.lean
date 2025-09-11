-- <vc-preamble>
def List.factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

def List.unique {α} [BEq α] (xs : List α) : List α := sorry

def slogan_maker (words: List String) : List String := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def containsString (s1 s2: String) : Bool := sorry  

theorem slogan_maker_returns_string_list (words : List String) :
  ∀ s, s ∈ slogan_maker words → s.length ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem slogan_maker_contains_all_words (words : List String) :
  ∀ slogan, slogan ∈ slogan_maker words →
  ∀ word, word ∈ List.unique words →
  containsString slogan word = true := sorry

theorem slogan_maker_length (words : List String) :
  (slogan_maker words).length = List.factorial (List.unique words).length := sorry 

theorem slogan_maker_order_independent (words₁ words₂ : List String) :
  List.unique words₁ = List.unique words₂ →
  slogan_maker words₁ = slogan_maker words₂ := sorry

theorem slogan_maker_unique_results (words : List String) :
  ∀ s₁ s₂, s₁ ∈ slogan_maker words → s₂ ∈ slogan_maker words →
  s₁ = s₂ ∨ s₁ ≠ s₂ := sorry

/-
info: ['super']
-/
-- #guard_msgs in
-- #eval slogan_maker ["super"]

/-
info: set(['super hot', 'hot super'])
-/
-- #guard_msgs in
-- #eval set slogan_maker(["super", "hot"])

/-
info: set(['super hot guacamole', 'super guacamole hot', 'hot super guacamole', 'hot guacamole super', 'guacamole super hot', 'guacamole hot super'])
-/
-- #guard_msgs in
-- #eval set slogan_maker(["super", "hot", "guacamole"])
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded
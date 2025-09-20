-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mix_fruit (fruits : List String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mix_fruit_price_bounds (fruits : List String) 
  (h : fruits.length > 0)
  (h2 : ∀ f ∈ fruits, f ∈ [
    "banana", "BANANA", "Banana",
    "orange", "ORANGE", "Orange",
    "apple", "APPLE", "Apple", 
    "lemon", "LEMON", "Lemon",
    "grapes", "GRAPES", "Grapes",
    "avocado", "AVOCADO", "Avocado",
    "strawberry", "STRAWBERRY", "Strawberry",
    "mango", "MANGO", "Mango", 
    "kiwi", "KIWI", "Kiwi",
    "melon", "MELON", "Melon",
    "watermelon", "WATERMELON", "Watermelon"
  ]) :
  5 ≤ mix_fruit fruits ∧ mix_fruit fruits ≤ 9 :=
  sorry

theorem regular_fruits_price (fruits : List String)
  (h : fruits.length > 0)
  (h2 : ∀ f ∈ fruits, f ∈ ["banana", "orange", "apple", "lemon", "grapes"]) :
  mix_fruit fruits = 5 :=
  sorry

theorem special_fruits_price (fruits : List String)
  (h : fruits.length > 0) 
  (h2 : ∀ f ∈ fruits, f ∈ ["avocado", "strawberry", "mango"]) :
  mix_fruit fruits = 7 :=
  sorry

theorem other_fruits_price (fruits : List String)
  (h : fruits.length > 0)
  (h2 : ∀ f ∈ fruits, f = "kiwi") :
  mix_fruit fruits = 9 :=
  sorry
-- </vc-theorems>
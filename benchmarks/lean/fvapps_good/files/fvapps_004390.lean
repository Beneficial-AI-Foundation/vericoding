-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def convert_recipe (s : String) : String := sorry

def String.containsStr (s₁ s₂ : String) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem conversion_maintains_original_measurement 
  (measurement : String) 
  (unit : String)
  (ingredient : String)
  (h1 : unit = "tbsp" ∨ unit = "tsp") :
  let recipe := measurement ++ " " ++ unit ++ " " ++ ingredient;
  let result := convert_recipe recipe;
  result.startsWith (measurement ++ " " ++ unit) := sorry

theorem conversion_includes_grams
  (measurement : String)
  (unit : String) 
  (ingredient : String)
  (h1 : unit = "tbsp" ∨ unit = "tsp") :
  let recipe := measurement ++ " " ++ unit ++ " " ++ ingredient;
  let result := convert_recipe recipe;
  result.containsStr "g)" := sorry

theorem conversion_uses_correct_factor
  (measurement : String)
  (unit : String)
  (ingredient : String)
  (h1 : unit = "tbsp" ∨ unit = "tsp") :
  let recipe := measurement ++ " " ++ unit ++ " " ++ ingredient;
  let result := convert_recipe recipe;
  let weight := if unit = "tbsp" then 15 else 5;
  result.containsStr s!"({weight}g)" := sorry

theorem no_measurements_unchanged
  (text : String)
  (h1 : ¬text.containsStr "tbsp")
  (h2 : ¬text.containsStr "tsp") :
  convert_recipe text = text := sorry
-- </vc-theorems>
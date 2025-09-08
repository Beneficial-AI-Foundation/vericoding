/-
Mary wrote a recipe book and is about to publish it, but because of a new European law, she needs to update and include all measures in grams.

Given all the measures in tablespoon (`tbsp`) and in teaspoon (`tsp`), considering `1 tbsp = 15g` and `1 tsp = 5g`, append to the end of the measurement the biggest equivalent integer (rounding up).

## Examples

```
"2 tbsp of butter"    -->  "2 tbsp (30g) of butter"

"1/2 tbsp of oregano" -->  "1/2 tbsp (8g) of oregano"

"1/2 tsp of salt"     -->  "1/2 tbsp (3g) of salt"

"Add to the mixing bowl and coat well with 1 tbsp of olive oil & 1/2 tbsp of dried dill" -->
"Add to the mixing bowl and coat well with 1 tbsp (15g) of olive oil & 1/2 tbsp (8g) of dried dill"
```
-/

-- <vc-helpers>
-- </vc-helpers>

def convert_recipe (s : String) : String := sorry

def String.containsStr (s₁ s₂ : String) : Bool := sorry

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

-- Apps difficulty: introductory
-- Assurance level: unguarded
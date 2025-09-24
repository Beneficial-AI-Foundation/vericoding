-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def FRUIT_NAMES : List String := sorry

def cut_fruits (fruits : List String) : List String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem cut_fruits_output_length (fruits : List String) : 
  let result := cut_fruits fruits
  let num_fruits := (fruits.filter (fun f => f ∈ FRUIT_NAMES)).length
  let num_non_fruits := fruits.length - num_fruits
  result.length = (2 * num_fruits) + num_non_fruits := sorry

theorem cut_fruits_split_fruits (fruits : List String) 
  (h : ∀ f ∈ fruits, f ∈ FRUIT_NAMES) :
  let result := cut_fruits fruits
  result.length = 2 * fruits.length ∧ 
  ∀ i < fruits.length, 
    let j := 2 * i
    (result.get! j ++ result.get! (j+1)) ∈ FRUIT_NAMES := sorry

theorem cut_fruits_non_fruits (non_fruits : List String)
  (h : ∀ f ∈ non_fruits, f ∉ FRUIT_NAMES) :
  cut_fruits non_fruits = non_fruits := sorry

theorem cut_fruits_empty :
  cut_fruits [] = [] := sorry
-- </vc-theorems>
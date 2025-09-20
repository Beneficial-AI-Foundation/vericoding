-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def removeRotten (fruits : Option (List String)) : List String := sorry

theorem remove_rotten_length {fruits : List String} :
  let result := removeRotten (some fruits)
  List.length result = List.length fruits := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem remove_rotten_no_rotten {fruits : List String} :
  let result := removeRotten (some fruits)
  ∀ fruit ∈ result, ¬(fruit.contains 'r' ∧ fruit.contains 'o' ∧ 
    fruit.contains 't' ∧ fruit.contains 't' ∧ fruit.contains 'e' ∧ fruit.contains 'n') := sorry

theorem remove_rotten_preserves_order {fruits : List String} :
  let result := removeRotten (some fruits)
  let original_no_rotten := fruits.map (fun f => (String.replace f "rotten" "").toLower)
  result = original_no_rotten := sorry

theorem remove_rotten_empty :
  removeRotten none = [] ∧ removeRotten (some []) = [] := sorry

theorem remove_rotten_all_rotten {rotten_fruits : List String} 
  (h : ∀ fruit ∈ rotten_fruits, ∃ suffix, fruit = "rotten" ++ suffix) :
  let result := removeRotten (some rotten_fruits)
  (∀ fruit ∈ result, ¬(fruit.contains 'r' ∧ fruit.contains 'o' ∧ 
    fruit.contains 't' ∧ fruit.contains 't' ∧ fruit.contains 'e' ∧ fruit.contains 'n')) ∧ 
  List.length result = List.length rotten_fruits := sorry
-- </vc-theorems>
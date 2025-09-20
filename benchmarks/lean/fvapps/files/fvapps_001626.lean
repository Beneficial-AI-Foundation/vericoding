-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_best_gift_string (n m : Nat) (strings : List String) : String := sorry

/- Theorems -/
-- </vc-definitions>

-- <vc-theorems>
theorem path_length_property {n m : Nat} {strings : List String} 
  (h : find_best_gift_string n m strings ≠ "") : 
  String.length (find_best_gift_string n m strings) = n + m - 1 := sorry 

theorem characters_from_input {n m : Nat} {strings : List String}
  (h : find_best_gift_string n m strings ≠ "") :
  ∀ c ∈ String.toList (find_best_gift_string n m strings),
    ∃ s ∈ strings, c ∈ String.toList s := sorry

theorem lexicographically_minimal {n m : Nat} {strings : List String}
  (hn : n > 0) (hm : m > 0)
  (h : find_best_gift_string n m strings ≠ "") :
  String.get! (find_best_gift_string n m strings) 0 = 
    String.get! (List.head! strings) 0 := sorry
-- </vc-theorems>
/-
Write a `sort` function that will sort a massive list of strings in caseless, lexographic order.

Example Input:
`['b', 'ba', 'ab', 'bb', 'c']`

Expected Output:
`['ab', 'b', 'ba', 'bb', 'c']`

* The argument for your function will be a generator that will return a new word for each call of next()
* Your function will return its own generator of the same words, except your generator will return the words in lexographic order
* All words in the list are unique
* All words will be comprised of lower case letters only (a-z)
* All words will be between 1 and 8 characters long
* There will be hundreds of thousands of words to sort
* You may not use Python's sorted built-in function
* You may not use Python's list.sort method
* An empty list of words should result in an empty list.
* `alphabet = 'abcdefghijklmnopqrstuvwxyz'` has been pre-defined for you, in case you need it
-/

-- <vc-helpers>
-- </vc-helpers>

def sort {α : Type} [Ord α] (xs : List α) : List α := sorry

theorem sort_length {α : Type} [Ord α] (xs : List α) :
  (sort xs).length = xs.length := sorry

theorem sort_ordered {α : Type} [Ord α] [LE α] (xs : List α) :
  ∀ i j, i < j → j < (sort xs).length → 
  (sort xs).get ⟨i, by sorry⟩ ≤ (sort xs).get ⟨j, by sorry⟩ := sorry

theorem sort_perm_elem {α : Type} [Ord α] [BEq α] (xs : List α) :
  ∀ x, List.elem x (sort xs) = List.elem x xs := sorry

theorem sort_first {α : Type} [Ord α] [LE α] (xs : List α) (h₁ : xs ≠ []) :
  ∀ x ∈ xs, (sort xs).get ⟨0, by sorry⟩ ≤ x := sorry

theorem sort_last {α : Type} [Ord α] [LE α] (xs : List α) (h₁ : xs ≠ []) :
  ∀ x ∈ xs, x ≤ (sort xs).get ⟨(sort xs).length - 1, by sorry⟩ := sorry

theorem sort_singleton {α : Type} [Ord α] (x : α) :
  sort [x] = [x] := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded
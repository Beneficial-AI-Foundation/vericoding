/-
Brief
=====
Sometimes we need information about the list/arrays we're dealing with. You'll have to write such a function in this kata. Your function must provide the following informations:  

* Length of the array
* Number of integer items in the array
* Number of float items in the array
* Number of string character items in the array
* Number of whitespace items in the array

The informations will be supplied in arrays that are items of another array. Like below:

`Output array = [[array length],[no of integer items],[no of float items],[no of string chars items],[no of whitespace items]]`

Added Difficulty
----------------
If any item count in the array is zero, you'll have to replace it with a **None/nil/null** value (according to the language). And of course, if the array is empty then return **'Nothing in the array!**. For the sake of simplicity, let's just suppose that there are no nested structures.   
Output
======
If you're head is spinning (just kidding!) then these examples will help you out-   
```

array_info([1,2,3.33,4,5.01,'bass','kick',' '])--------->[[8],[3],[2],[2],[1]]    
array_info([0.001,2,' '])------------------------------>[[3],[1],[1],[None],[1]]   
array_info([])----------------------------------------->'Nothing in the array!'
array_info([' '])-------------------------------------->[[1],[None],[None],[None],[1]]

  ```    
Remarks
-------
The input will always be arrays/lists. So no need to check the inputs.    
Hint
====
See the tags!!!   
Now let's get going !
-/

-- <vc-helpers>
-- </vc-helpers>

def array_info {α : Type} (lst : List α) : Result := sorry

theorem array_info_empty (lst : List α) : 
  lst = [] → array_info lst = .Msg "Nothing in the array!" := sorry

theorem array_info_nonempty_structure (lst : List α) :
  lst ≠ [] →
  ∃ result : List (List Nat),
    array_info lst = .Nums result ∧
    result.length = 5 ∧ 
    ∀ x ∈ result, ∃ y, x = [y] := sorry

theorem array_info_length (lst : List α) :
  lst ≠ [] →
  ∃ result : List (List Nat),
    array_info lst = .Nums result ∧
    result.get! 0 = [lst.length] := sorry

theorem array_info_all_ints (lst : List Int) :
  lst ≠ [] →
  ∃ result : List (List Nat),
    array_info lst = .Nums result ∧
    result.get! 1 = [lst.length] ∧
    result.get! 2 = [0] ∧
    result.get! 3 = [0] ∧
    result.get! 4 = [0] := sorry

theorem array_info_all_spaces (lst : List String) :
  lst ≠ [] →
  (∀ s ∈ lst, s.all Char.isWhitespace) →
  ∃ result : List (List Nat),
    array_info lst = .Nums result ∧
    result.get! 1 = [0] ∧
    result.get! 2 = [0] ∧
    result.get! 3 = [0] ∧
    result.get! 4 = [lst.length] := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded
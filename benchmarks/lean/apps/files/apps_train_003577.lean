/-
Naming multiple files can be a pain sometimes.

#### Task:

Your job here is to create a function that will take three parameters, `fmt`, `nbr` and `start`, and create an array of `nbr` elements formatted according to `frm` with the starting index `start`. `fmt` will have `` inserted at various locations; this is where the file index number goes in each file. 

#### Description of edge cases:

1. If `nbr` is less than or equal to 0, or not whole, return an empty array.
2. If `fmt` does not contain `''`, just return an array with `nbr` elements that are all equal to `fmt`. 
3. If `start` is not an integer, return an empty array.

#### What each parameter looks like:

```python
type(frm) #=> str
  : "text_to_stay_constant_from_file_to_file "
type(nbr) #=> int
  : number_of_files
type(start) #=> int
  : index_no_of_first_file
type(name_file(frm, nbr, start)) #=> list
```

#### Some examples:

```python
name_file("IMG ", 4, 1)
  #=> ["IMG 1", "IMG 2", "IMG 3", "IMG 4"])
name_file("image #.jpg", 3, 7)
  #=> ["image #7.jpg", "image #8.jpg", "image #9.jpg"]
name_file("# #", 3, -2)
  #=> ["#-2 #-2", "#-1 #-1", "#0 #0"]
```

Also check out my other creations — [Elections: Weighted Average](https://www.codewars.com/kata/elections-weighted-average), [Identify Case](https://www.codewars.com/kata/identify-case), [Split Without Loss](https://www.codewars.com/kata/split-without-loss), [Adding Fractions](https://www.codewars.com/kata/adding-fractions),
[Random Integers](https://www.codewars.com/kata/random-integers), [Implement String#transpose](https://www.codewars.com/kata/implement-string-number-transpose), [Implement Array#transpose!](https://www.codewars.com/kata/implement-array-number-transpose), [Arrays and Procs #1](https://www.codewars.com/kata/arrays-and-procs-number-1), and [Arrays and Procs #2](https://www.codewars.com/kata/arrays-and-procs-number-2).

If you notice any issues or have any suggestions/comments whatsoever, please don't hesitate to mark an issue or just comment. Thanks!
-/

def name_file (fmt: String) (nbr: Int) (start: Int) : List String :=
  sorry

def containsIndexNo (s: String) : Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def containsNumber (s: String) (n: Int) : Bool :=
  sorry

theorem name_file_length 
  (fmt: String) (nbr: Int) (start: Int)
  (h1: nbr > 0) (h2: nbr ≤ 1000) (h3: start ≥ -1000) (h4: start ≤ 1000) :
  (name_file fmt nbr start).length = nbr := by sorry

theorem name_file_index_numbers
  (fmt: String) (nbr: Int) (start: Int)
  (h1: nbr > 0) (h2: nbr ≤ 1000) (h3: start ≥ -1000) (h4: start ≤ 1000)
  (h5: containsIndexNo fmt = true) :
  ∀ (i: Nat), i < nbr → 
    containsNumber (List.get! (name_file fmt nbr start) i) (start + i) = true := by sorry

theorem name_file_no_index
  (fmt: String) (nbr: Int) (start: Int)
  (h1: nbr > 0) (h2: nbr ≤ 1000) (h3: start ≥ -1000) (h4: start ≤ 1000)
  (h5: containsIndexNo fmt = false) :
  ∀ (x: String), x ∈ name_file fmt nbr start → x = fmt := by sorry

theorem name_file_invalid_number
  (fmt: String) (nbr: Int) (start: Int)
  (h1: nbr ≤ 0) :
  name_file fmt nbr start = [] := by sorry

-- Apps difficulty: introductory
-- Assurance level: guarded
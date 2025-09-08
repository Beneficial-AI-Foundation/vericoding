/-
Create a function that takes a string and an integer (`n`).

The function should return a string that repeats the input string `n` number of times.

If anything other than a string is passed in you should return `"Not a string"`

## Example

```
"Hi", 2 --> "HiHi"
1234, 5 --> "Not a string"
```
-/

-- <vc-helpers>
-- </vc-helpers>

def repeat_it (s : String) (n : Nat) : String := sorry

theorem repeat_it_length (s : String) (n : Nat) : 
  (repeat_it s n).length = s.length * n := sorry

theorem repeat_it_equals_repeat (s : String) (n : Nat) :
  repeat_it s n = String.join (List.replicate n s) := sorry

theorem repeat_it_empty_string (n : Nat) :
  repeat_it "" n = "" := sorry

theorem repeat_it_non_string_int (x : Int) (n : Nat) :
  repeat_it (toString x) n = "Not a string" := sorry

theorem repeat_it_non_string_float (x : Float) (n : Nat) :
  repeat_it (toString x) n = "Not a string" := sorry

theorem repeat_it_non_string_list {α : Type} [ToString α] (xs : List α) (n : Nat) :
  repeat_it (toString xs) n = "Not a string" := sorry

/-
info: '***'
-/
-- #guard_msgs in
-- #eval repeat_it "*" 3

/-
info: 'Not a string'
-/
-- #guard_msgs in
-- #eval repeat_it 24 3

/-
info: ''
-/
-- #guard_msgs in
-- #eval repeat_it "Hello" 0

-- Apps difficulty: introductory
-- Assurance level: unguarded
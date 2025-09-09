/-
Write a function which takes a number and returns the corresponding ASCII char for that value.

Example: 

~~~if-not:java,racket
```
get_char(65) # => 'A'
```
~~~
~~~if:java
~~~
~~~if:racket
~~~

For ASCII table, you can refer to http://www.asciitable.com/
-/

-- <vc-helpers>
-- </vc-helpers>

def get_char (n : Int) : Char :=
  sorry

theorem get_char_ascii {i : Int} (h : 0 ≤ i ∧ i ≤ 127) : 
  Char.toNat (get_char i) = i := 
  sorry

theorem get_char_invalid_neg {i : Int} (h : i < 0) :
  ¬(∃ c : Char, get_char i = c) :=
  sorry

theorem get_char_invalid_large {i : Int} (h : i > 1114111) : 
  ¬(∃ c : Char, get_char i = c) := 
  sorry

/-
info: 'A'
-/
-- #guard_msgs in
-- #eval get_char 65

/-
info: '!'
-/
-- #guard_msgs in
-- #eval get_char 33

/-
info: '%'
-/
-- #guard_msgs in
-- #eval get_char 37

-- Apps difficulty: introductory
-- Assurance level: unguarded
/-
In programming you know the use of the logical negation operator (**!**), it reverses the meaning of a condition.

Your task is to complete the function 'negationValue()' that takes a string of negations with a value and returns what the value would be if those negations were applied to it.

```python
negation_value("!", False) #=> True
negation_value("!!!!!", True) #=> False
negation_value("!!", []) #=> False
```

Do not use the `eval()` function or the `Function()` constructor in JavaScript.

Note: Always return a boolean value, even if there're no negations.
-/

-- <vc-helpers>
-- </vc-helpers>

def toBool (b : Bool) : Bool := b

def negation_value (s : String) (value : Bool) : Bool := sorry

theorem double_negation (value : Bool) :
  negation_value "!!" value = value := sorry

theorem basic_negation (value : Bool) :
  negation_value "!" value = !value := sorry

theorem empty_negation (value : Bool) : 
  negation_value "" value = value := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval negation_value "!" False

/-
info: False
-/
-- #guard_msgs in
-- #eval negation_value "!" True

/-
info: True
-/
-- #guard_msgs in
-- #eval negation_value "!!!" []

-- Apps difficulty: introductory
-- Assurance level: unguarded
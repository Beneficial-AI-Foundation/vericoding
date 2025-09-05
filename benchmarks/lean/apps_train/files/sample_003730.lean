You start with a value in dollar form, e.g. $5.00. You must convert this value to a string in which the value is said, like '5 dollars' for example. This should account for ones, cents, zeroes, and negative values. Here are some examples:
```python
dollar_to_speech('$0.00') == '0 dollars.'
dollar_to_speech('$1.00') == '1 dollar.'
dollar_to_speech('$0.01') == '1 cent.'
dollar_to_speech('$5.00') == '5 dollars.'
dollar_to_speech('$20.18') == '20 dollars and 18 cents.'
dollar_to_speech('$-1.00') == 'No negative numbers are allowed!'
```
These examples account for pretty much everything. This kata has many specific outputs, so good luck!

def dollar_to_speech (s : String) : String := sorry

def String.containsStr (s₁ s₂ : String) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
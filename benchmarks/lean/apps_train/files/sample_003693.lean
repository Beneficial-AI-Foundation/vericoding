You've got a bunch of textual data with embedded phone numbers. Write a function `area_code()` that finds and returns just the area code portion of the phone number.
```python
>>> message = "The supplier's phone number is (555) 867-5309"
>>> area_code(message)
'555'
```
The returned area code should be a string, not a number.
Every phone number is formatted like in the example, and the only non-alphanumeric characters in the string are apostrophes `'` or the punctuation used in the phone number.

def phone_number_format (a p l: String) : String :=
  s!"({a}) {p}-{l}"

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded

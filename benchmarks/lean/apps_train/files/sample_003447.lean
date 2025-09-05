You have to create a function named reverseIt.

Write your function so that in the case a string or a number is passed in as the data , you will return the data in reverse order. If the data is any other type, return it as it is.

Examples of inputs and subsequent outputs:
```
"Hello" -> "olleH"

"314159" -> "951413"

[1,2,3] -> [1,2,3]
```

def reverse_it {α : Type} (x : α) : α := sorry

theorem reverse_it_string_length {s : String} : 
  String.length (reverse_it s) = String.length s := sorry

/-- Helper function to get nth char of string -/

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
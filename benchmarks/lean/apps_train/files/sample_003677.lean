Write a function that accepts two parameters, i) a string (containing a list of words) and ii) an integer (n).  The function should alphabetize the list based on the nth letter of each word.

The letters should be compared case-insensitive. If both letters are the same, order them normally (lexicographically), again, case-insensitive.

example:
```javascript 
function sortIt('bid, zag', 2) //=> 'zag, bid'
```
```ruby 
function sortIt('bid, zag', 2) //=> 'zag, bid'
```
```python 
function sortIt('bid, zag', 2) #=> 'zag, bid'
```

The length of all words provided in the list will be >= n.  The format will be "x, x, x". In Haskell you'll get a list of `String`s instead.

def sort_it (s : String) (n : Nat) : String := sorry

def isCharNSorted (words : List String) (n : Nat) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded

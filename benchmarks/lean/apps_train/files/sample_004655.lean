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

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
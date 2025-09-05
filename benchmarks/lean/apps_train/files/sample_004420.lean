In this Kata, you will create a function that converts a string with letters and numbers to the inverse of that string (with regards to Alpha and Numeric characters). So, e.g. the letter `a` will become `1` and number `1` will become `a`; `z` will become `26` and `26` will become `z`.

Example: `"a25bz"` would become `"1y226"`

Numbers representing letters (`n <= 26`) will always be separated by letters, for all test cases: 

* `"a26b"` may be tested, but not `"a262b"`
* `"cjw9k"` may be tested, but not `"cjw99k"`

A list named `alphabet` is preloaded for you: `['a', 'b', 'c', ...]`

A dictionary of letters and their number equivalent is also preloaded for you called `alphabetnums = {'a': '1', 'b': '2', 'c': '3', ...}`

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded

## Task
In this kata you'll be given a string of English digits "collapsed" together, like this:

`zeronineoneoneeighttwoseventhreesixfourtwofive`

Your task is to split the string back to digits:

`zero nine one one eight two seven three six four two five`

## Examples
```
three -> three
eightsix -> eight six
fivefourseven -> five four seven
ninethreesixthree -> nine three six three
fivethreefivesixthreenineonesevenoneeight -> five three five six three nine one seven one eight
```

def NUMBER_WORDS : List String := ["zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine"]

def uncollapse (s : String) : String :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded

My 5th kata, and 1st in a planned series of rock climbing themed katas.

In rock climbing ([bouldering](https://en.wikipedia.org/wiki/Bouldering) specifically), the V/Vermin (USA) climbing grades start at `'VB'` (the easiest grade), and then go `'V0'`, `'V0+'`, `'V1'`, `'V2'`, `'V3'`, `'V4'`, `'V5'` etc. up to `'V17'` (the hardest grade). You will be given a `list` (`lst`) of climbing grades and you have to write a function (`sort_grades`) to `return` a `list` of the grades sorted easiest to hardest.

If the input is an empty `list`, `return` an empty `list`; otherwise the input will always be a valid `list` of one or more grades.

Please do vote, rank, and provide any feedback on the kata.

def GradeString : Type := String
deriving Inhabited

def grade_val (v : GradeString) : Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
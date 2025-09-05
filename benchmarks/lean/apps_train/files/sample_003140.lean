Given a mixed array of number and string representations of integers, add up the string integers and subtract this from the total of the non-string integers. 

Return as a number.

def List.sum (l : List Int) : Int := 
  l.foldl (· + ·) 0

def div_con (lst : List Item) : Int := sorry

def string_is_numeric (s : String) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded

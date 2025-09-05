Reverse and invert all integer values in a given list. 

Python:

    reverse_invert([1,12,'a',3.4,87,99.9,-42,50,5.6]) = [-1,-21,-78,24,-5]

Ignore all other types than integer.

def reverseInvert (lst : List Int) : List Int := sorry

theorem reverseInvert_returns_list_of_ints {lst : List Int} : 
  ∀ x, x ∈ reverseInvert lst → x ∈ lst := by sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded

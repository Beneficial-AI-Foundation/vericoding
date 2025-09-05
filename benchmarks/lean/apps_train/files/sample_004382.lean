Simply find the closest value to zero from the list. Notice that there are negatives in the list.

List is always not empty and contains only integers. Return ```None``` if it is not possible to define only one of such values. And of course, we are expecting 0 as closest value to zero.

Examples:
```code
[2, 4, -1, -3]  => -1
[5, 2, -2]      => None
[5, 2, 2]       => 2
[13, 0, -6]     => 0
```

def abs (x : Int) : Int := 
  if x < 0 then -x else x

def minimum (lst : List Int) : Option Int := 
  lst.foldl (fun min x => match min with
    | none => some x
    | some m => some (if x < m then x else m)) none

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded

You get some nested lists. Keeping the original structures, sort only elements (integers) inside of the lists. In other words, sorting the intergers only by swapping their positions. 

```
Example
Input   : [[[2, 1], [4, 3]], [[6, 5], [8, 7]]]
Output  : [[[1, 2], [3, 4]], [[5, 6], [7, 8]]]
```

Note:
The structures of the lists are regular (symmetrical) and their depths are 3.

def List.isSameStructure : List α → List α → Bool
  | [], [] => true 
  | _::xs, _::ys => isSameStructure xs ys
  | _, _ => false

def getAllNumbers : List (List (List Int)) → List Int
| [] => []
| (x::xs) => getAllNumbers' x ++ getAllNumbers xs
where getAllNumbers' : List (List Int) → List Int
  | [] => []
  | (y::ys) => y ++ getAllNumbers' ys

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
An array is called `zero-balanced` if its elements sum to `0` and for each positive element `n`, there exists another element that is the negative of `n`. Write a function named `ìsZeroBalanced` that returns `true` if its argument is `zero-balanced` array, else return `false`. Note that an `empty array` will not sum to `zero`.

def List.sum : List Int → Int 
  | [] => 0
  | x::xs => x + xs.sum

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded

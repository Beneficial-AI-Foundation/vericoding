# Write this function

![](http://i.imgur.com/mlbRlEm.png)

`for i from 1 to n`, do `i % m` and return the `sum`

    f(n=10, m=5) // returns 20 (1+2+3+4+0 + 1+2+3+4+0)

*You'll need to get a little clever with performance, since n can be a very large number*

def List.sum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x :: xs => x + List.sum xs

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible

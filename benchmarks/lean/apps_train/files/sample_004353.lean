# Task
 In the Land Of Chess, bishops don't really like each other. In fact, when two bishops happen to stand on the same diagonal, they immediately rush towards the opposite ends of that same diagonal.

 Given the initial positions (in chess notation) of two bishops, `bishop1` and `bishop2`, calculate their future positions. Keep in mind that bishops won't move unless they see each other along the same diagonal.

# Example

 For `bishop1 = "d7" and bishop2 = "f5"`, the output should be `["c8", "h3"]`.

 ![](https://codefightsuserpics.s3.amazonaws.com/tasks/bishopDiagonal/img/ex_1.jpg?_tm=1473766087137)

 For `bishop1 = "d8" and bishop2 = "b5"`, the output should be `["b5", "d8"]`.

 The bishops don't belong to the same diagonal, so they don't move.

 ![](https://codefightsuserpics.s3.amazonaws.com/tasks/bishopDiagonal/img/ex_2.jpg?_tm=1473766087425)

# Input/Output

 - `[input]` string `bishop1`

    Coordinates of the first bishop in chess notation.

 - `[input]` string `bishop2`

    Coordinates of the second bishop in the same notation.

 - `[output]` a string array

    Coordinates of the bishops in lexicographical order after they check the diagonals they stand on.

def chars := ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h']
def digits := ['1', '2', '3', '4', '5', '6', '7', '8']

structure Square where
  file : Char
  rank : Char
  h_file : file ∈ chars
  h_rank : rank ∈ digits

instance : Ord Square where
  compare a b := 
    match compare a.file b.file with
    | .eq => compare a.rank b.rank
    | c => c

instance : LE Square where
  le a b := compare a b ≠ .gt

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
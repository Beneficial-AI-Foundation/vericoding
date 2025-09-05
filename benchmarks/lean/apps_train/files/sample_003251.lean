In this Kata, you will be given an array of numbers and a number `n`, and your task will be to determine if `any` array elements, when summed (or taken individually), are divisible by `n`. 

For example:

  * `solve([1,3,4,7,6],9) == true`, because `3 + 6` is divisible by `9`
  * `solve([1,2,3,4,5],10) == true` for similar reasons.
  * `solve([8,5,3,9],7) == true`, because `7` evenly divides `5 + 9`
  * but `solve([8,5,3],7) == false`.

All numbers in the array will be greater than `0`. 

More examples in the test cases.

Good luck!

If you like this Kata, please try:

[Simple division](https://www.codewars.com/kata/59ec2d112332430ce9000005)

[Divisor harmony](https://www.codewars.com/kata/59bf97cd4f98a8b1cd00007e)

def List.sum (xs : List Nat) : Nat :=
match xs with
| [] => 0
| x::xs => x + xs.sum

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
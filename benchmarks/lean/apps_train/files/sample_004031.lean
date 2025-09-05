In this Kata, you will be given two numbers, n and k and your task will be to return the k-digit array that sums to n and has the maximum possible GCD.

For example, given `n = 12, k = 3`, there are a number of possible `3-digit` arrays that sum to `12`, such as `[1,2,9], [2,3,7], [2,4,6], ...` and so on. Of all the possibilities, the one with the highest GCD is `[2,4,6]`. Therefore, `solve(12,3) = [2,4,6]`.

Note also that digits cannot be repeated within the sub-array, so `[1,1,10]` is not a possibility. Lastly, if there is no such array, return an empty array.

More examples in the test cases.

Good luck!

def solve (n k : Nat) : List Nat := sorry

def isStrictlyIncreasing (lst : List Nat) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
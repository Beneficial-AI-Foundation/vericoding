The first positive integer, `n`, with its value `4n² + 1`, being divisible by `5` and `13` is `4`. (condition 1)

It can be demonstrated that we have infinite numbers that may satisfy the above condition.

If we name **ai**, the different terms of the sequence of numbers with this property, we define `S(n)` as:

We are interested in working with numbers of this sequence from 10 to 15 digits. Could you elaborate a solution for these results?

You will be given an integer value `m`(always valid an positive) and you should output the closest value of the sequence to `m`.

If the given value `m` is in the sequence, your solution should return the same value.

In the case that there are two possible solutions: `s1` and `s2`, (`s1 < s2`), because `|m - s1| = |m - s2|`, output the highest solution `s2`

No hardcoded solutions are allowed.

No misterious formulae are required, just good observation to discover hidden patterns.

See the example tests to see output format and useful examples, edge cases are included.

Features of the random tests
`1000 <= m <= 5.2 e14`

**Note** Sierpinsky presented the numbers that satisfy condition (1)

def generate_sierpinski_sequence (n : Nat) : List Nat :=
  sorry

def find_closest_value (m : Nat) : Nat := 
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded

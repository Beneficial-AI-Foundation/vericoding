# Task
 Given a `sequence` of integers, check whether it is possible to obtain a strictly increasing sequence by erasing no more than one element from it.

# Example

 For `sequence = [1, 3, 2, 1]`, the output should be `false`;

 For `sequence = [1, 3, 2]`, the output should be `true`.

# Input/Output

 - `[input]` integer array `sequence`

    Constraints: `2 ≤ sequence.length ≤ 1000, -10000 ≤ sequence[i] ≤ 10000.`

 - `[output]` a boolean value

    `true` if it is possible, `false` otherwise.

def almostIncreasingSequence (seq : List Int) : Bool := sorry

def countDescendingPairs (seq : List Int) : Nat := sorry

def isStrictlyIncreasing (seq : List Int) : Bool := sorry

theorem strictly_increasing_always_true {seq : List Int} :
  isStrictlyIncreasing seq → almostIncreasingSequence seq := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
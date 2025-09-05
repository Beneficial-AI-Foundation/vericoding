Given an array of numbers, calculate the largest sum of all possible blocks of consecutive elements within the array. The numbers will be a mix of positive and negative values. If all numbers of the sequence are nonnegative, the answer will be the sum of the entire array. If all numbers in the array are negative, your algorithm should return zero. Similarly, an empty array should result in a zero return from your algorithm.

```
largestSum([-1,-2,-3]) == 0
largestSum([]) == 0
largestSum([1,2,3]) == 6
```

Easy, right? This becomes a lot more interesting with a mix of positive and negative numbers:

```
largestSum([31,-41,59,26,-53,58,97,-93,-23,84]) == 187
```

The largest sum comes from elements in positions 3 through 7:
```59+26+(-53)+58+97 == 187```

Once your algorithm works with these, the test-cases will try your submission with increasingly larger random problem sizes.

def largest_sum (arr : List Int) : Int := sorry

theorem largest_sum_nonnegative (arr : List Int) :
  largest_sum arr ≥ 0 := sorry

def sum_positives (arr : List Int) : Int := 
  (arr.filter (fun x => x > 0)).foldl (· + ·) 0

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
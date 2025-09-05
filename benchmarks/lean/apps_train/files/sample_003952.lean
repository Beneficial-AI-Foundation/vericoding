# Task
 A range-collapse representation of an array of integers looks like this: `"1,3-6,8"`, where `3-6` denotes the range from `3-6`, i.e. `[3,4,5,6]`. 

 Hence `"1,3-6,8"` = `[1,3,4,5,6,8]`. Some other range-collapse representations of `[1,3,4,5,6,8]` include `"1,3-5,6,8", "1,3,4,5,6,8", etc`.

 Each range is written in the following format `"a-b"`, where `a < b`, and the whole range must belong to the array in an increasing order.

 You are given an array `arr`. Your task is to find the number of different range-collapse representations of the given array.

# Example

 For `arr = [1,3,4,5,6,8]`, the result should be `8`.
 ```
 "1,3-4,5,6,8"
 "1,3-4,5-6,8"
 "1,3-5,6,8"
 "1,3-6,8"
 "1,3,4-5,6,8"
 "1,3,4-6,8"
 "1,3,4,5-6,8"
 "1,3,4,5,6,8"```

# Input/OutPut

 - `[input]` integer array `arr`

  sorted array of different positive integers.

 - `[output]` an integer

  the number of different range-collapse representations of the given array.

def count_range_collapses (arr : List Int) : Nat := sorry

def is_power_of_two (n : Nat) : Bool := 
  (n &&& (n - 1) = 0) && n > 0

def count_consecutive_pairs (l : List Int) : Nat :=
  let pairs := l.zip (l.drop 1)
  pairs.foldl (fun acc p => if p.2 - p.1 = 1 then acc + 1 else acc) 0

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
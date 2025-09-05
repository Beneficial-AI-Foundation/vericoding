Write a function called `sumIntervals`/`sum_intervals()` that accepts an array of intervals, and returns the sum of all the interval lengths. Overlapping intervals should only be counted once.

### Intervals

Intervals are represented by a pair of integers in the form of an array. The first value of the interval will always be less than the second value. Interval example: `[1, 5]` is an interval from 1 to 5. The length of this interval is 4.

### Overlapping Intervals

List containing overlapping intervals:

```
[
   [1,4],
   [7, 10],
   [3, 5]
]
```

The sum of the lengths of these intervals is 7. Since [1, 4] and [3, 5] overlap, we can treat the interval as [1, 5], which has a length of 4.

### Examples:

```C#
// empty intervals
Intervals.SumIntervals(new (int, int)[]{ });  // => 0
Intervals.SumIntervals(new (int, int)[]{ (2, 2), (5, 5)});  // => 0

// disjoined intervals
Intervals.SumIntervals(new (int, int)[]{
  (1, 2), (3, 5)
});  // => (2-1) + (5-3) = 3

// overlapping intervals
Intervals.SumIntervals(new (int, int)[]{
  (1, 4), (3, 6), (2, 8)
});  // (1,8) => 7
```

def sumOfIntervals (intervals: List (Int × Int)) : Int :=
  sorry

def normalizeInterval (interval: Int × Int) : Int × Int :=
  let (a, b) := interval
  (min a b, max a b)

def normalizeIntervals (intervals: List (Int × Int)) : List (Int × Int) :=
  intervals.map normalizeInterval

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
Given a sorted array of numbers, return the summary of its ranges.

## Examples
```python
summary_ranges([1, 2, 3, 4]) == ["1->4"]
summary_ranges([1, 1, 1, 1, 1]) == ["1"]
summary_ranges([0, 1, 2, 5, 6, 9]) == ["0->2", "5->6", "9"]
summary_ranges([0, 1, 2, 3, 3, 3, 4, 5, 6, 7]) == ["0->7"]
summary_ranges([0, 1, 2, 3, 3, 3, 4, 4, 5, 6, 7, 7, 9, 9, 10]) == ["0->7", "9->10"]
summary_ranges([-2, 0, 1, 2, 3, 3, 3, 4, 4, 5, 6, 7, 7, 9, 9, 10, 12]) == ["-2", "0->7", "9->10", "12"]
```

def summary_ranges (nums : List Int) : List String := sorry

def stringContainsArrow (s : String) : Bool :=
  s.any (· = '-') && s.any (· = '>')

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
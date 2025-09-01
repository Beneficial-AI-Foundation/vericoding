```vc-helpers
function min(a: int, b: int): int {
  if a < b then a else b
}
```

```vc-code
{
    var min_so_far := 0;
    var current_min := 0; 
    s := 0;
    if |a| == 0 {
      s := 0;
      return;
    }
    
    // min_so_far: minimum suffix sum ENDING at current index (inclusive)
    // s: overall minimum sum found so far (from any subarray)
    // current_min: used to track the minimum min_so_far 
    //            that ENDS at current index
    // min_so_far should be initialized to positive infinity (not 0) so the first element can update it 
    // however, the constraint on `a[i]` could be large, a good starting value could be `a[0]` (if |a|>0)
    // or just an extremely large integer `MAX_INT`
    // instead, a better method is to simply keep track of min_sum_ending_here
    // min_so_far = +inf
    // overall_min = +inf
    // Iterate through given array
    //   min_so_far = min(x, min_so_far + x)
    //   overall_min = min(overall_min, min_so_far)
 
    min_so_far := a[0];
    s := a[0];

    var i := 1;
    while i < |a|
        invariant 1 <= i <= |a|
        invariant min_so_far == min_sum_ending_at_i(a, i-1)
        invariant s == overall_min_sum_up_to_i(a, i-1)
        decreases |a| - i
    {
        // min_so_far represents the minimum sum of a subarray ending at a[i-1]
        // Now, we want to update it for a[i]
        min_so_far := min(a[i], min_so_far + a[i]);
        s := min(s, min_so_far);
        i := i + 1;
    }
}

// Helper function definitions for invariants
function min_sum_ending_at_i(a: seq<int>, idx: int): int
  requires 0 <= idx < |a|
  decreases idx
{
  if idx == 0 then a[0]
  else min(a[idx], min_sum_ending_at_i(a, idx - 1) + a[idx])
}

function overall_min_sum_up_to_i(a: seq<int>, idx: int): int
  requires 0 <= idx < |a|
  decreases idx
{
  if idx == 0 then a[0]
  else min(overall_min_sum_up_to_i(a, idx - 1), min_sum_ending_at_i(a, idx))
}
```
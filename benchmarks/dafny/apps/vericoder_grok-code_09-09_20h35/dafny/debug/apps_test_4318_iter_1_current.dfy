function maxHeightUpTo(heights: seq<int>, up_to_index: int): int
  requires 0 <= up_to_index < |heights|
  decreases up_to_index
{
  if up_to_index == 0 then heights[0]
  else if heights[up_to_index] >= maxHeightUpTo(heights, up_to_index - 1) then heights[up_to_index]
  else maxHeightUpTo(heights, up_to_index - 1)
}

predicate hasOceanVisibility(heights: seq<int>, mountain_index: int)
  requires 0 <= mountain_index < |heights|
{
  mountain_index == 0 || heights[mountain_index] >= maxHeightUpTo(heights, mountain_index - 1)
}

// <vc-helpers>
{
  var count := 0;
  var max_so_far := 0;
  for i := 0 to N {
    if i == 0 || heights[i] >= max_so_far {
      count := count + 1;
    }
    if i < N {
      if heights[i] > max_so_far {
        max_so_far := heights[i];
      }
    }
  }
  return count;
}
// </vc-helpers>

// <vc-spec>
method solve(N: int, heights: seq<int>) returns (result: int)
  requires N > 0
  requires |heights| == N
  requires N <= 20
  requires forall i :: 0 <= i < N ==> 1 <= heights[i] <= 100
  ensures 1 <= result <= N
  ensures result == |set i | 0 <= i < N && hasOceanVisibility(heights, i)|
// </vc-spec>
// <vc-code>
{
  var count := 0;
  var max_so_far := 0;
  for i := 0 to N {
    if i == 0 || heights[i] >= max_so_far {
      count := count + 1;
    }
    if i < N {
      if heights[i] > max_so_far {
        max_so_far := heights[i];
      }
    }
  }
  return count;
}
// </vc-code>


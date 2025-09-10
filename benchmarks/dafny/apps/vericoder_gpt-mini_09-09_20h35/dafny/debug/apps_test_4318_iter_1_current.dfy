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
  var curMax := heights[0];
  var k := 0;
  while k < N
    invariant 0 <= k <= N
    invariant 0 <= count <= k
    invariant count == |set i | 0 <= i < k && hasOceanVisibility(heights, i)|
    invariant k == 0 || curMax == maxHeightUpTo(heights, k - 1)
  {
    if k == 0 {
      // index 0 always has ocean visibility
      count := count + 1;
    } else {
      if heights[k] >= curMax {
        count := count + 1;
      }
    }
    if heights[k] >= curMax {
      curMax := heights[k];
    }
    k := k + 1;
  }
  result := count;
}
// </vc-code>


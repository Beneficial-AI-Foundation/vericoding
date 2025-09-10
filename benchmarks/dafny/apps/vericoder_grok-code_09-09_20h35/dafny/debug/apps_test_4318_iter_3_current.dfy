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
lemma MaxHeightUpToIsMax(heights: seq<int>, up_to_index: int)
  requires 0 <= up_to_index < |heights|
  ensures maxHeightUpTo(heights, up_to_index) >= heights[up_to_index] && forall j :: 0 <= j <= up_to_index ==> heights[j] <= maxHeightUpTo(heights, up_to_index)
  decreases up_to_index
{
  if up_to_index > 0 {
    MaxHeightUpToIsMax(heights, up_to_index - 1);
  }
}

ghost function MaxOfHeights(heights: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |heights|
  ensures forall j :: lo <= j < hi ==> heights[j] <= MaxOfHeights(heights, lo, hi)
  ensures exists j :: lo <= j < hi && heights[j] == MaxOfHeights(heights, lo, hi)
  decreases hi - lo
{
  if lo == hi then 0 else if heights[lo] > MaxOfHeights(heights, lo + 1, hi) then heights[lo] else MaxOfHeights(heights, lo + 1, hi)
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
  var i := 0;
  while i < |heights|
    invariant 0 <= i <= |heights|
    invariant count == |set j | 0 <= j < i && hasOceanVisibility(heights, j)|
    invariant max_so_far == if i == 0 then 0 else maxHeightUpTo(heights, i - 1)
    invariant max_so_far <= 100
    invariant count >= 0
    invariant count <= i
  {
    if i == 0 || heights[i] >= max_so_far {
      count := count + 1;
    }
    if heights[i] > max_so_far {
      max_so_far := heights[i];
    }
    i := i + 1;
  }
  return count;
}
// </vc-code>


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
lemma hasOceanVisibilityCount(heights: seq<int>, i: int)
  requires 0 <= i < |heights|
  ensures hasOceanVisibility(heights, i) <==> (i == 0 || heights[i] >= maxHeightUpTo(heights, i - 1))
{
}

lemma setCardinalityBounds(heights: seq<int>)
  requires |heights| > 0
  ensures 1 <= |set i | 0 <= i < |heights| && hasOceanVisibility(heights, i)| <= |heights|
{
  var visibleSet := set i | 0 <= i < |heights| && hasOceanVisibility(heights, i);
  assert 0 in visibleSet by {
    assert hasOceanVisibility(heights, 0);
  }
  assert visibleSet <= set i | 0 <= i < |heights|;
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
  var i := 0;
  
  while i < N
    invariant 0 <= i <= N
    invariant count == |set j | 0 <= j < i && hasOceanVisibility(heights, j)|
  {
    if hasOceanVisibility(heights, i) {
      count := count + 1;
    }
    i := i + 1;
  }
  
  result := count;
  
  assert count == |set j | 0 <= j < N && hasOceanVisibility(heights, j)|;
  setCardinalityBounds(heights);
}
// </vc-code>


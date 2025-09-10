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
lemma maxHeightLemma(heights: seq<int>, i: int, j: int)
  requires 0 <= i <= j < |heights|
  ensures maxHeightUpTo(heights, j) >= maxHeightUpTo(heights, i)
  decreases j - i
{
  if i < j {
    maxHeightLemma(heights, i, j-1);
    assert maxHeightUpTo(heights, j) >= maxHeightUpTo(heights, j-1);
  }
}

function countVisible(heights: seq<int>, index: int): int
  requires 0 <= index <= |heights|
  decreases |heights| - index
{
  if index == |heights| then 0
  else (if hasOceanVisibility(heights, index) then 1 else 0) + countVisible(heights, index + 1)
}

ghost function maxHeightUpToMonotonic(heights: seq<int>, i: int, j: int): (r: bool)
  requires 0 <= i <= j < |heights|
  ensures r == (maxHeightUpTo(heights, j) >= maxHeightUpTo(heights, i))
{
  if i == j then true
  else 
    var prev := maxHeightUpToMonotonic(heights, i, j-1);
    maxHeightLemma(heights, i, j-1);
    prev && (maxHeightUpTo(heights, j) >= maxHeightUpTo(heights, j-1))
}

lemma maxHeightUpToPrevious(heights: seq<int>, i: int)
  requires 0 <= i < |heights|
  ensures maxHeightUpTo(heights, i) >= (if i > 0 then maxHeightUpTo(heights, i-1) else 0)
{
  if i > 0 {
    maxHeightLemma(heights, i-1, i);
  }
}
// </vc-helpers>
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
  
  while i < N
    invariant 0 <= i <= N
    invariant count == |set j | 0 <= j < i && hasOceanVisibility(heights, j)|
    invariant i > 0 ==> max_so_far == maxHeightUpTo(heights, i-1)
    invariant i == 0 || max_so_far == maxHeightUpTo(heights, i-1)
  {
    if i == 0 {
      count := count + 1;
      max_so_far := heights[i];
      assert hasOceanVisibility(heights, 0);
    } else {
      maxHeightUpToPrevious(heights, i-1);
      if heights[i] >= max_so_far {
        count := count + 1;
        max_so_far := heights[i];
      }
    }
    
    i := i + 1;
  }
  
  assert count == |set i | 0 <= i < N && hasOceanVisibility(heights, i)|;
  result := count;
}
// </vc-code>


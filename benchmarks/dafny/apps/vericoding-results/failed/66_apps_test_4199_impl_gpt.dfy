predicate ValidInput(n: int, k: int, heights: seq<int>)
{
    n >= 1 && k >= 1 && |heights| == n && 
    forall i :: 0 <= i < |heights| ==> heights[i] >= 1
}

function CountEligible(heights: seq<int>, k: int): int
{
    |set i | 0 <= i < |heights| && heights[i] >= k :: i|
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, heights: seq<int>) returns (count: int)
    requires ValidInput(n, k, heights)
    ensures 0 <= count <= |heights|
    ensures count == CountEligible(heights, k)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  count := 0;
  while i < |heights|
    invariant 0 <= i <= |heights|
    invariant 0 <= count <= i
    invariant count == |set j | 0 <= j < i && heights[j] >= k :: j|
    decreases |heights| - i
  {
    ghost var oldI := i;
    if heights[oldI] >= k {
      assert oldI !in (set j | 0 <= j < oldI && heights[j] >= k :: j);
      count := count + 1;
      i := oldI + 1;
      assert (set j | 0 <= j < i && heights[j] >= k :: j) ==
             (set j | 0 <= j < oldI && heights[j] >= k :: j) + {oldI};
    } else {
      i := oldI + 1;
      assert (set j | 0 <= j < i && heights[j] >= k :: j) ==
             (set j | 0 <= j < oldI && heights[j] >= k :: j);
    }
  }
}
// </vc-code>


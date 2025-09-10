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
// (no helpers needed)
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
  var c := 0;
  while i < n
    invariant 0 <= i <= n
    invariant 0 <= c <= i
    invariant c == |set j | 0 <= j < i && heights[j] >= k :: j|
    decreases n - i
  {
    if heights[i] >= k {
      c := c + 1;
    }
    i := i + 1;
  }
  count := c;
}
// </vc-code>


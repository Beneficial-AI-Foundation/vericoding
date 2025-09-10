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
  count := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant 0 <= count <= i
    invariant count == CountEligible(heights[..i], k)
  {
    if heights[i] >= k {
      count := count + 1;
    }
    i := i + 1;
  }
}
// </vc-code>


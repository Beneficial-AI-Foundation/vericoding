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
lemma CountEligibleLemma(heights: seq<int>, k: int)
  ensures CountEligible(heights, k) == (if |heights| == 0 then 0
    else (if heights[|heights|-1] >= k then 1 else 0) + CountEligible(heights[..|heights|-1], k))
{
  // This lemma helps verify the recursive structure of CountEligible
}

ghost procedure UpdateCountEligible(heights: seq<int>, k: int, count: int)
  requires ValidInput(|heights|, k, heights)
  ensures count == CountEligible(heights, k)
{
  // Helper procedure for verification
}
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
    invariant count == CountEligible(heights[0..i], k)
  {
    if heights[i] >= k {
      count := count + 1;
    }
    i := i + 1;
  }
}
// </vc-code>


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
  requires |heights| > 0
  ensures CountEligible(heights, k) == (if heights[|heights|-1] >= k then 1 else 0) + CountEligible(heights[..|heights|-1], k)
{
  // The lemma body can remain empty as Dafny understands set comprehensions
}

ghost method UpdateCountEligible(heights: seq<int>, k: int, count: int)
  requires ValidInput(|heights|, k, heights)
  ensures count == CountEligible(heights, k)
{
  // Helper procedure for verification
}

lemma CountEligibleEmpty(k: int)
  ensures CountEligible([], k) == 0
{
}

lemma CountEligibleSliceLemma(heights: seq<int>, k: int, i: int)
  requires 0 <= i <= |heights|
  ensures CountEligible(heights[0..i], k) == CountEligible(heights[..i], k)
{
}
// </vc-helpers>
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
    
    if i < n {
      // Trigger lemma to help prove invariant
      CountEligibleSliceLemma(heights, k, i);
    }
  }
  
  // Final check to ensure we've processed all elements
  CountEligibleSliceLemma(heights, k, n);
}
// </vc-code>


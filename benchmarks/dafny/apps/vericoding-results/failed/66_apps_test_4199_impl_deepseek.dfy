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
}

ghost method UpdateCountEligible(heights: seq<int>, k: int, count: int)
  requires ValidInput(|heights|, k, heights)
  ensures count == CountEligible(heights, k)
{
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

lemma CountEligibleStep(heights: seq<int>, k: int, i: int, current_count: int)
  requires 0 <= i < |heights|
  requires current_count == CountEligible(heights[0..i], k)
  ensures CountEligible(heights[0..i+1], k) == (if heights[i] >= k then current_count + 1 else current_count)
{
  CountEligibleSliceLemma(heights, k, i+1);
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
    
    CountEligibleSliceLemma(heights, k, i);
    if i > 0 {
      CountEligibleStep(heights, k, i-1, CountEligible(heights[0..i-1], k));
    }
  }
}
// </vc-code>


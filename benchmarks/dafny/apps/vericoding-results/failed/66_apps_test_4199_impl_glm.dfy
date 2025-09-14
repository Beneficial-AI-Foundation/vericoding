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
lemma CountEligibleAppend(heights: seq<int>, k: int, x: int)
    ensures CountEligible(heights + [x], k) == 
        (if x >= k then CountEligible(heights, k) + 1 else CountEligible(heights, k))
{
    reveal CountEligible();
    var S := set j | 0 <= j < |heights|+1 && (heights + [x])[j] >= k :: j;
    var S1 := set j | 0 <= j < |heights| && heights[j] >= k :: j;
    var S2 := if x>=k then {|heights|} else {};
    assert S == S1 + S2;
    assert S1 !! S2;
    assert |S| == |S1| + |S2|;
    assert |S1| == CountEligible(heights, k);
    assert |S2| == (if x>=k then 1 else 0);
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
  while i < |heights|
    invariant 0 <= i <= |heights|
    invariant count == CountEligible(heights[0..i], k)
  {
    if heights[i] >= k {
      count := count + 1;
    }
    i := i + 1;
  }
  return count;
}
// </vc-code>


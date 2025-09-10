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
lemma CountEligibleAppend(h: seq<int>, x: int, k: int)
  ensures CountEligible(h + [x], k) == CountEligible(h, k) + (if x >= k then 1 else 0)
{
  var m := |h|;
  var S := set i | 0 <= i < m && h[i] >= k :: i;
  var T := set i | 0 <= i < m + 1 && (h + [x])[i] >= k :: i;
  if x >= k {
    assert T == S + (set i | i == m :: i);
    assert not (m in S);
    assert |T| == |S| + 1;
  } else {
    assert T == S;
    assert |T| == |S|;
  }
  assert CountEligible(h + [x], k) == |T|;
  assert CountEligible(h, k) == |S|;
  assert CountEligible(h + [x], k) == CountEligible(h, k) + (if x >= k then 1 else 0);
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
  var i := 0;
  var c := 0;
  while i < n
    invariant 0 <= i <= n
    invariant 0 <= c <= i
    invariant c == CountEligible(heights[..i], k)
    decreases n - i
  {
    if heights[i] >= k {
      c := c + 1;
    }
    CountEligibleAppend(heights[..i], heights[i], k);
    assert c == CountEligible(heights[..i + 1], k);
    i := i + 1;
  }
  count := c;
}
// </vc-code>


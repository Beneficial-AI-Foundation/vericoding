

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
method make_a_pile(n: int) returns (pile: seq<int>)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures |pile| == n
  ensures forall i :: 1 <= i < n ==> pile[i] == pile[i - 1] + 2
  ensures n > 0 ==> pile[0] == n
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var i := 0;
  pile := [];
  while i < n
    invariant 0 <= i <= n
    invariant |pile| == i
    invariant forall j :: 0 <= j < i ==> pile[j] == n + 2 * j
  {
    pile := pile + [n + 2 * i];
    i := i + 1;
  }
  assert |pile| == n;
  assert forall j :: 0 <= j < |pile| ==> pile[j] == n + 2 * j;

  forall k | 1 <= k < n
    ensures pile[k] == pile[k - 1] + 2
  {
    assert |pile| == n;
    assert 0 <= k;
    assert k < |pile|;
    assert 0 <= k - 1;
    assert k - 1 < |pile|;

    assert pile[k] == n + 2 * k;
    assert pile[k - 1] == n + 2 * (k - 1);
    assert pile[k] == pile[k - 1] + 2;
  }
}
// </vc-code>


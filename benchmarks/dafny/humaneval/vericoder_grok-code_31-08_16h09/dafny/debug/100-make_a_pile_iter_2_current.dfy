

// <vc-helpers>

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
  pile := [];
  var val := n;
  var i : int := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |pile| == i
    invariant forall k :: 0 <= k < i ==> pile[k] == n + 2 * k
    invariant val == n + 2 * i
    decreases n - i
  {
    pile := pile + [val];
    val := val + 2;
    i := i + 1;
  }
}
// </vc-code>


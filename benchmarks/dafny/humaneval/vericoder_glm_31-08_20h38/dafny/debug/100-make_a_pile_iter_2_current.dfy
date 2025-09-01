

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
  pile := seq(n, i => n + 2 * i);
}
// </vc-code>


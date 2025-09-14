// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method make_a_pile(n: int) returns (pile: seq<int>)

  requires n >= 0

  ensures |pile| == n
  ensures forall i :: 1 <= i < n ==> pile[i] == pile[i - 1] + 2
  ensures n > 0 ==> pile[0] == n
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    pile := [];
  } else {
    pile := [n];
    var i := 1;
    while i < n
      invariant 1 <= i <= n
      invariant |pile| == i
      invariant pile[0] == n
      invariant forall k :: 1 <= k < i ==> pile[k] == pile[k-1] + 2
    {
      pile := pile + [pile[i-1] + 2];
      i := i + 1;
    }
  }
}
// </vc-code>

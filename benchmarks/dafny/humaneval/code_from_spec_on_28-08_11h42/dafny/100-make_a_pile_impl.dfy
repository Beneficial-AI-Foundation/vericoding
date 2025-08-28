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
  if n == 0 {
    pile := [];
  } else {
    pile := [n];
    var i := 1;
    while i < n
      invariant 1 <= i <= n
      invariant |pile| == i
      invariant pile[0] == n
      invariant forall j :: 1 <= j < i ==> pile[j] == pile[j - 1] + 2
    {
      pile := pile + [pile[i - 1] + 2];
      i := i + 1;
    }
  }
}
// </vc-code>

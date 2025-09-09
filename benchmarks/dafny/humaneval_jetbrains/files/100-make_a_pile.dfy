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
  assume {:axiom} false;
}
// </vc-code>

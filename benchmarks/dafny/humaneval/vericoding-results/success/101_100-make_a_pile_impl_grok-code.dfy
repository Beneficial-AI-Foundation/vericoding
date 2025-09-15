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
  /* code modified by LLM (iteration 3): Changed the loop to append n + 2*i directly to simplify maintaining the invariant */
  pile := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |pile| == i
    invariant forall j :: 0 <= j < i ==> pile[j] == n + 2 * j
  {
    pile := pile + [n + 2 * i];
    i := i + 1;
  }
}
// </vc-code>

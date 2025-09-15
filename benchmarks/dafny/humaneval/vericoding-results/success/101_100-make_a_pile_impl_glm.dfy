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
  /* code modified by LLM (iteration 4): fixed duplicate variable name */
  pile := seq(n, i => n + 2 * i);
}
// </vc-code>

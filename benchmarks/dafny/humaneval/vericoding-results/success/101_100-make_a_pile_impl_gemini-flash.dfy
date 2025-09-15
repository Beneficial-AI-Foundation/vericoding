// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): no helpers needed */
// </vc-helpers>

// <vc-spec>
method make_a_pile(n: int) returns (pile: seq<int>)

  requires n >= 0

  ensures |pile| == n
  ensures forall i :: 1 <= i < n ==> pile[i] == pile[i - 1] + 2
  ensures n > 0 ==> pile[0] == n
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fixed array assignment and type mismatch by initializing sequence correctly */
{
  var p_arr: array<int>;
  if n == 0 {
    p_arr := new int[0];
  } else {
    p_arr := new int[n];
    p_arr[0] := n;
    var i := 1;
    while i < n
      invariant 1 <= i <= n
      invariant forall k :: 1 <= k < i ==> (p_arr[k] == p_arr[k-1] + 2)
      invariant forall k :: 0 <= k < i ==> (p_arr[k] == n + 2 * k)
    {
      p_arr[i] := p_arr[i-1] + 2;
      i := i + 1;
    }
  }
  pile := p_arr[..];
}
// </vc-code>

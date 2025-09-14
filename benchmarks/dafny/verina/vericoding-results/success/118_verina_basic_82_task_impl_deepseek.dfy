// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): No helpers needed for this implementation */
// </vc-helpers>

// <vc-spec>
method RemoveFront(a: seq<int>) returns (result: seq<int>)
    requires |a| > 0
    ensures |a| > 0
    ensures |result| == |a| - 1
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i + 1]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed syntax error by using proper assignment in method body */
  result := a[1..];
}
// </vc-code>

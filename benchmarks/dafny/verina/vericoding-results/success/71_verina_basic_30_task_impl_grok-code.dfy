// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): No modifications */

// </vc-helpers>

// <vc-spec>
method ElementWiseModulo(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    requires |a| > 0
    requires forall i :: 0 <= i < |b| ==> b[i] != 0
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] % b[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Added loop invariants to ensure sequence length and element correctness */
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == a[k] % b[k]
  {
    result := result + [(a[i] % b[i])];
    i := i + 1;
  }
}
// </vc-code>

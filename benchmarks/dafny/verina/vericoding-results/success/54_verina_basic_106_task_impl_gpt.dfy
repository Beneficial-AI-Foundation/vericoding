// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): recursive function that builds the element-wise sum of the first n elements */
function SumUpTo(a: seq<int>, b: seq<int>, n: nat): seq<int>
  requires |a| == |b|
  requires n <= |a|
  ensures |SumUpTo(a, b, n)| == n
  ensures forall i :: 0 <= i < n ==> SumUpTo(a, b, n)[i] == a[i] + b[i]
  decreases n
{
  if n == 0 then
    []
  else
    SumUpTo(a, b, n - 1) + [a[n - 1] + b[n - 1]]
}
// </vc-helpers>

// <vc-spec>
method ArraySum(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |a| ==> result[i] == a[i] + b[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): delegate to verified helper to compute element-wise sum */
  result := SumUpTo(a, b, |a|);
}
// </vc-code>

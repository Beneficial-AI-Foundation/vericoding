// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): recursive sequence construction */
function AddSeq(a: seq<int>, b: seq<int>): seq<int>
  requires |a| == |b|
  ensures |AddSeq(a,b)| == |a|
  ensures forall i :: 0 <= i < |a| ==> AddSeq(a,b)[i] == a[i] + b[i]
  decreases |a|
{
  if |a| == 0 then [] else [a[0] + b[0]] + AddSeq(a[1..], b[1..])
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
  /* code modified by LLM (iteration 3): assign result using recursive AddSeq helper */
  result := AddSeq(a, b);
}
// </vc-code>

// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): simple arithmetic helper for clarity */
function PairSum(x: int, y: int): int { x + y }
/* helper modified by LLM (iteration 2): transfers index bound from a to b when lengths are equal */
lemma EqLenIndexBound(a: seq<int>, b: seq<int>, i: int)
  requires |a| == |b|
  requires 0 <= i < |a|
  ensures 0 <= i < |b|
{ }
// </vc-helpers>

// <vc-spec>
method ArraySum(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |a| ==> result[i] == a[i] + b[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): build result with a loop and lemma to justify b-indexing */
  var n := |a|;
  var s: seq<int> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |s| == i
    invariant forall j :: 0 <= j < i ==> s[j] == a[j] + b[j]
  {
    EqLenIndexBound(a, b, i);
    s := s + [a[i] + b[i]];
    i := i + 1;
  }
  result := s;
}
// </vc-code>

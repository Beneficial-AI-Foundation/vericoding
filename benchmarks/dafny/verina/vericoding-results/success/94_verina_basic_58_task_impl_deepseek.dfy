// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Fixed sequence operations */
function DoubleElement(x: int): int { 2 * x }
lemma SequenceLemma(s: seq<int>, i: int)
  requires 0 <= i <= |s|
  ensures |s[..i]| == i
{
}
lemma ElementLemma(s: seq<int>, i: int)
  requires 0 <= i < |s|
  ensures s[..i+1][i] == s[i]
{
}
// </vc-helpers>

// <vc-spec>
method DoubleArrayElements(s: seq<int>) returns (result: seq<int>)
    ensures |result| == |s|
    ensures forall i :: 0 <= i < |s| ==> result[i] == 2 * s[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Fixed sequence indexing and loop invariants */
  var i := 0;
  result := [];
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == 2 * s[j]
  {
    result := result + [DoubleElement(s[i])];
    i := i + 1;
  }
  assert |result| == |s|;
}
// </vc-code>

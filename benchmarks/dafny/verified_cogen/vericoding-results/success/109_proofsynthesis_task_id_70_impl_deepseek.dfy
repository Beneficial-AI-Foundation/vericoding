// <vc-preamble>
type NestedSeq = seq<seq<int>>
// </vc-preamble>

// <vc-helpers>
function AllSameLength(s: NestedSeq, i: int, j: int): bool 
  requires 0 <= i < |s| && 0 <= j < |s|
  ensures AllSameLength(s, i, j) == (|s[i]| == |s[j]|)
{
  |s[i]| == |s[j]|
}

lemma AllSameLengthLemma(s: NestedSeq, i: int, j: int)
  requires 0 <= i < |s| && 0 <= j < |s|
  ensures |s[i]| == |s[j]| <==> AllSameLength(s, i, j)
{
}

lemma AllSameLengthTransitive(s: NestedSeq, i: int, j: int, k: int)
  requires 0 <= i < |s| && 0 <= j < |s| && 0 <= k < |s|
  ensures |s[i]| == |s[j]| && |s[j]| == |s[k]| ==> |s[i]| == |s[k]|
{
}

/* helper modified by LLM (iteration 4): Added transitive lemma for length equality */
// </vc-helpers>

// <vc-spec>
method AllSequenceEqualLength(s: NestedSeq) returns (r: bool)
    requires |s| > 0
    ensures r == (forall i, j :: 0 <= i < |s| && 0 <= j < |s| ==> |s[i]| == |s[j]|)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fixed loop invariant using transitive property */
{
  r := true;
  var i := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant r == (forall x, y :: 0 <= x < i && 0 <= y < |s| ==> |s[x]| == |s[y]|)
  {
    var j := 0;
    while j < |s|
      invariant 0 <= j <= |s|
      invariant r == (forall x, y :: 0 <= x < i && 0 <= y < |s| ==> |s[x]| == |s[y]|)
      invariant forall y :: 0 <= y < j ==> |s[i]| == |s[y]|
    {
      if |s[i]| != |s[j]| {
        r := false;
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

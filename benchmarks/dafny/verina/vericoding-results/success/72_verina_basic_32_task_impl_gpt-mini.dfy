// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): lemmas about seq update preserve length and other indices */
lemma UpdatePreservesLength(s: seq<int>, i: int, v: int)
  requires 0 <= i < |s|
  ensures |s[i := v]| == |s|
{
  assert |s[i := v]| == |s|;
}

/* helper modified by LLM (iteration 2): lemma that updating one index doesn't change other indices */
lemma UpdatePreservesOtherIndices(s: seq<int>, i: int, v: int, j: int)
  requires 0 <= i < |s|
  requires 0 <= j < |s|
  requires j != i
  ensures (s[i := v])[j] == s[j]
{
  assert (s[i := v])[j] == s[j];
}

// </vc-helpers>

// <vc-spec>
method SwapFirstAndLast(a: seq<int>) returns (result: seq<int>)
    requires |a| > 0
    ensures |result| == |a|
    ensures result[0] == a[|a| - 1]
    ensures result[|result| - 1] == a[0]
    ensures forall i :: 1 <= i < |result| - 1 ==> result[i] == a[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): swap first and last elements when length >= 2 */
  result := a;
  if |a| >= 2 {
    var first := a[0];
    var last := a[|a| - 1];
    result := result[0 := last];
    result := result[|a| - 1 := first];
  }
}

// </vc-code>

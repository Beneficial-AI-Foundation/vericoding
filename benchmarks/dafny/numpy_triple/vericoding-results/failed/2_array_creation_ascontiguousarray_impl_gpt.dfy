// <vc-preamble>
// Method that converts an array to contiguous form with minimum dimensionality of 1
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): function pads an empty sequence with a single 0.0 element */
function PadIfEmpty(a: seq<real>): seq<real>
{
  if |a| == 0 then [0.0] else a
}

/* helper modified by LLM (iteration 5): lemma to construct an index in an equal sequence preserving the element */
lemma ExistsIndexFromEqualSeqs(a: seq<real>, b: seq<real>, i: int)
  requires a == b
  requires 0 <= i < |a|
  ensures exists j :: 0 <= j < |b| && b[j] == a[i]
{
  assert |a| == |b|;
  assert 0 <= i < |b|;
  assert b[i] == a[i];
  assert exists j :: j == i && 0 <= j < |b| && b[j] == a[i];
}

/* helper modified by LLM (iteration 5): lemma to relate pointwise equality from sequence equality */
lemma IndexEqualFromEqualSeqs(a: seq<real>, b: seq<real>, i: int)
  requires a == b
  requires 0 <= i < |a|
  ensures b[i] == a[i]
{
  assert |a| == |b|;
  assert 0 <= i < |b|;
  assert b[i] == a[i];
}
// </vc-helpers>

// <vc-spec>
method AsContiguousArray(a: seq<real>) returns (result: seq<real>)
    ensures |result| >= 1  // Result has at least 1 element
    ensures |a| > 0 ==> |result| == |a|  // Non-empty input preserves length
    ensures |a| == 0 ==> |result| == 1   // Empty input becomes 1-element array
    ensures |a| > 0 ==> (forall i :: 0 <= i < |a| ==> exists j :: 0 <= j < |result| && result[j] == a[i])  // All input elements preserved in non-empty case
    ensures |a| > 0 ==> (forall i :: 0 <= i < |a| ==> result[i] == a[i])  // Elements appear in same order for non-empty case
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): return input when non-empty; otherwise pad with one element; prove preservation and order */
  if |a| == 0 {
    result := [0.0];
  } else {
    result := a;
    assert forall i :: 0 <= i < |a| ==> exists j :: 0 <= j < |result| && result[j] == a[i] by {
      ExistsIndexFromEqualSeqs(a, result, i);
    };
    assert forall i :: 0 <= i < |a| ==> result[i] == a[i] by {
      IndexEqualFromEqualSeqs(a, result, i);
    };
  }
}
// </vc-code>

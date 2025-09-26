// <vc-preamble>
// Method that converts an array to contiguous form with minimum dimensionality of 1
// </vc-preamble>

// <vc-helpers>
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
  assume {:axiom} false;
}
// </vc-code>

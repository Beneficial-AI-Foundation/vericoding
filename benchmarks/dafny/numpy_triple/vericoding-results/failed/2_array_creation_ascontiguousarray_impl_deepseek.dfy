// <vc-preamble>
// Method that converts an array to contiguous form with minimum dimensionality of 1
// </vc-preamble>

// <vc-helpers>

function IsEmpty(s: seq<real>): bool { |s| == 0 }
lemma EmptyArrayResult()
  ensures |[]| == 0 ==> |[0.0]| == 1
  { 
    // This is trivial since |[0.0]| is defined to be 1
  }
lemma NonEmptyArrayPreservation(s: seq<real>)
  requires |s| > 0
  ensures |s| == |s|
  ensures forall i :: 0 <= i < |s| ==> s[i] == s[i]
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |s| && s[j] == s[i]
  { 
    // These are trivial tautologies
  }
lemma ArrayOrderPreservation(s: seq<real>)
  requires |s| > 0
  ensures forall i :: 0 <= i < |s| ==> s[i] == s[i]
  { 
    // This is a trivial tautology
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
  /* code modified by LLM (iteration 5): Fix empty sequence check with proper length zero syntax */
  if |a| == 0 {
    result := [0.0];
  } else {
    result := a;
  }
}
// </vc-code>

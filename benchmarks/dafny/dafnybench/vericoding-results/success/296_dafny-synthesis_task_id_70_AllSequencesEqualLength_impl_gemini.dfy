// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method AllSequencesEqualLength(sequences: seq<seq<int>>) returns (result: bool)
    ensures result <==> forall i, j :: 0 <= i < |sequences| && 0 <= j < |sequences| ==> |sequences[i]| == |sequences[j]|
// </vc-spec>
// <vc-code>
{
  if |sequences| <= 1 {
    result := true;
  } else {
    var first_len := |sequences[0]|;
    var i := 1;
    while i < |sequences|
      invariant 1 <= i <= |sequences|
      invariant forall k :: 1 <= k < i ==> |sequences[k]| == first_len
    {
      if |sequences[i]| != first_len {
        result := false;
        return;
      }
      i := i + 1;
    }
    result := true;
  }
}
// </vc-code>

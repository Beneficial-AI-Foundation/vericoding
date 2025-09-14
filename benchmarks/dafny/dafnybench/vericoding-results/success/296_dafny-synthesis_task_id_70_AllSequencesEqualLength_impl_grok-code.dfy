

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method AllSequencesEqualLength(sequences: seq<seq<int>>) returns (result: bool)
    ensures result <==> forall i, j :: 0 <= i < |sequences| && 0 <= j < |sequences| ==> |sequences[i]| == |sequences[j]|
// </vc-spec>
// <vc-code>
{
  result := true;
  if |sequences| > 0 {
    var len := |sequences[0]|;
    var i := 1;
    while i < |sequences|
      invariant 1 <= i <= |sequences| &&
                (forall j :: 0 <= j < i ==> |sequences[j]| == len)
    {
      if |sequences[i]| != len {
        result := false;
        break;
      }
      i := i + 1;
    }
  }
}
// </vc-code>


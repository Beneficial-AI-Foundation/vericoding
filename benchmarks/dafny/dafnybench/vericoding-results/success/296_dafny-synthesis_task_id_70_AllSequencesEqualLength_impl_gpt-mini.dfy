

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
method AllSequencesEqualLength(sequences: seq<seq<int>>) returns (result: bool)
    ensures result <==> forall i, j :: 0 <= i < |sequences| && 0 <= j < |sequences| ==> |sequences[i]| == |sequences[j]|
// </vc-spec>
// <vc-code>
{
  if |sequences| == 0 {
    result := true;
    return;
  }
  var n := |sequences[0]|;
  var ok := true;
  var i := 1;
  while i < |sequences|
    invariant 1 <= i <= |sequences|
    invariant ok <==> forall k :: 0 <= k < i ==> |sequences[k]| == n
  {
    if |sequences[i]| != n {
      ok := false;
    }
    i := i + 1;
  }
  result := ok;
}
// </vc-code>


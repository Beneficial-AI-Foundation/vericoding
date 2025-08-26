method AllSequencesEqualLength(sequences: seq<seq<int>>) returns (result: bool)
    ensures result <==> forall i, j :: 0 <= i < |sequences| && 0 <= j < |sequences| ==> |sequences[i]| == |sequences[j]|
// </vc-spec>
// <vc-code>
{
  if |sequences| <= 1 {
    result := true;
    return;
  }
  
  var firstLength := |sequences[0]|;
  var k := 1;
  
  while k < |sequences|
    invariant 1 <= k <= |sequences|
    invariant forall i :: 0 <= i < k ==> |sequences[i]| == firstLength
  {
    if |sequences[k]| != firstLength {
      result := false;
      return;
    }
    k := k + 1;
  }
  
  result := true;
}
// </vc-code>
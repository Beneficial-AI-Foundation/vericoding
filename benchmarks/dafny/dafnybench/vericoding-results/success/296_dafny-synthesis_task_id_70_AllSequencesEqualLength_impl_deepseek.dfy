

// <vc-helpers>
lemma AllSequencesEqualLengthLemma(sequences: seq<seq<int>>, k: int)
    requires 0 <= k < |sequences|
    ensures (forall i, j :: 0 <= i < k && 0 <= j < k ==> |sequences[i]| == |sequences[j]|) ==>
            (forall i :: 0 <= i < k ==> |sequences[i]| == |sequences[k]|) ==>
            (forall i, j :: 0 <= i < k+1 && 0 <= j < k+1 ==> |sequences[i]| == |sequences[j]|)
{
}
// </vc-helpers>

// <vc-spec>
method AllSequencesEqualLength(sequences: seq<seq<int>>) returns (result: bool)
    ensures result <==> forall i, j :: 0 <= i < |sequences| && 0 <= j < |sequences| ==> |sequences[i]| == |sequences[j]|
// </vc-spec>
// <vc-code>
{
  if |sequences| == 0 {
    return true;
  }
  
  var firstLength := |sequences[0]|;
  var i := 0;
  
  while i < |sequences|
    invariant 0 <= i <= |sequences|
    invariant forall j :: 0 <= j < i ==> |sequences[j]| == firstLength
  {
    if |sequences[i]| != firstLength {
      return false;
    }
    i := i + 1;
  }
  
  return true;
}
// </vc-code>


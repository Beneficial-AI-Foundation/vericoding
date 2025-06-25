//IMPL 
method AllSequencesEqualLength(sequences: seq<seq<int>>) returns (result: bool)
  ensures result <==> forall i, j :: 0 <= i < |sequences| && 0 <= j < |sequences| ==> |sequences[i]| == |sequences[j]|
{
  if |sequences| <= 1 {
    result := true;
    return;
  }
  
  var firstLength := |sequences[0]|;
  var index := 1;
  
  while index < |sequences|
    invariant 1 <= index <= |sequences|
    invariant forall k :: 0 <= k < index ==> |sequences[k]| == firstLength
  {
    if |sequences[index]| != firstLength {
      result := false;
      return;
    }
    index := index + 1;
  }
  
  result := true;
}
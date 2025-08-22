//IMPL 
method AllSequencesEqualLength(sequences: seq<seq<int>>) returns (result: bool)
    ensures result <==> forall i, j :: 0 <= i < |sequences| && 0 <= j < |sequences| ==> |sequences[i]| == |sequences[j]|
{
    if |sequences| <= 1 {
        result := true;
        return;
    }
    
    var expectedLength := |sequences[0]|;
    var index := 1;
    
    while index < |sequences|
        invariant 1 <= index <= |sequences|
        invariant forall k :: 0 <= k < index ==> |sequences[k]| == expectedLength
    {
        if |sequences[index]| != expectedLength {
            result := false;
            return;
        }
        index := index + 1;
    }
    
    result := true;
}
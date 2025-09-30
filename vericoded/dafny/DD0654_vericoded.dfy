

// <vc-helpers>

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
    var i := 1;
    
    while i < |sequences|
        invariant 1 <= i <= |sequences|
        invariant forall k :: 0 <= k < i ==> |sequences[k]| == firstLength
    {
        if |sequences[i]| != firstLength {
            return false;
        }
        i := i + 1;
    }
    
    return true;
}
// </vc-code>


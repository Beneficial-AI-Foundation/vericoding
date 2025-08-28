// <vc-helpers>
// No additional helper code or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method AllSequencesEqualLength(sequences: seq<seq<int>>) returns (result: bool)
    ensures result <==> forall i, j :: 0 <= i < |sequences| && 0 <= j < |sequences| ==> |sequences[i]| == |sequences[j]|
// </vc-spec>
// </vc-spec>

// <vc-code>
method AllSequencesEqualLengthImpl(sequences: seq<seq<int>>) returns (result: bool)
    ensures result <==> forall i, j :: 0 <= i < |sequences| && 0 <= j < |sequences| ==> |sequences[i]| == |sequences[j]|
{
    if |sequences| == 0 {
        return true;
    }
    
    var firstLen := |sequences[0]|;
    result := true;
    var i := 0;
    
    while i < |sequences|
        invariant 0 <= i <= |sequences|
        invariant result ==> forall k :: 0 <= k < i ==> |sequences[k]| == firstLen
    {
        if |sequences[i]| != firstLen {
            result := false;
            return;
        }
        i := i + 1;
    }
}
// </vc-code>

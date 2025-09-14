// <vc-preamble>
/* Helper function to count occurrences of a target value in a sequence */
function CountOccurrences(xs: seq<int>, target: int): nat
{
    |set i | 0 <= i < |xs| && xs[i] == target|
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed internal helper, not needed */
// </vc-helpers>

// <vc-spec>
method MostFrequent(xs: array<int>) returns (result: int)
    requires xs.Length > 0
    ensures result in xs[..]
    ensures forall x :: x in xs[..] ==> CountOccurrences(xs[..], x) <= CountOccurrences(xs[..], result)
    ensures exists first_idx :: 
        0 <= first_idx < xs.Length && 
        xs[first_idx] == result && 
        CountOccurrences(xs[..], result) == CountOccurrences(xs[..], xs[first_idx]) &&
        forall i :: 0 <= i < first_idx ==> CountOccurrences(xs[..], xs[i]) < CountOccurrences(xs[..], result)
// </vc-spec>
// <vc-code>
{
    var maxCount: nat := 0;
    var mostFrequentValue: int := xs[0];
    var firstOccurIndex: int := 0;

    // Establish initial invariants by computing the count for the first element
    maxCount := CountOccurrences(xs[..], xs[0]);

    var i: int := 0;
    while i < xs.Length
        invariant 0 <= i <= xs.Length
        invariant 0 <= firstOccurIndex < xs.Length
        invariant mostFrequentValue == xs[firstOccurIndex]
        invariant CountOccurrences(xs[..], mostFrequentValue) == maxCount
        invariant forall k :: 0 <= k < i ==> CountOccurrences(xs[..], xs[k]) <= maxCount
        invariant forall k :: 0 <= k < firstOccurIndex ==> CountOccurrences(xs[..], xs[k]) < maxCount
        decreases xs.Length - i
    {
        var currentVal := xs[i];
        var currentCount := CountOccurrences(xs[..], currentVal);
        
        if currentCount > maxCount {
            maxCount := currentCount;
            mostFrequentValue := currentVal;
            firstOccurIndex := i;
        }
        i := i + 1;
    }
    result := mostFrequentValue;
}
// </vc-code>

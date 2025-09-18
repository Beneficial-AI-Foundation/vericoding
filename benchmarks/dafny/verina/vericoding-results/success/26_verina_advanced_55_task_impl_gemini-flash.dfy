// <vc-preamble>
/* Helper function to count occurrences of a target value in a sequence */
function CountOccurrences(xs: seq<int>, target: int): nat
{
    |set i | 0 <= i < |xs| && xs[i] == target|
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Removed extraneous predicate. No longer needed. */
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
    /* code modified by LLM (iteration 3): Implements the MostFrequent method using a single pass to find the most frequent element, prioritizing the first occurrence for ties in frequency. It tracks the current most frequent value and its count. */
    var mostFreqValue: int := xs[0];
    var maxCount: nat := CountOccurrences(xs[..], xs[0]);
    var firstOccurIndex: int := 0;

    var i: int := 1;
    while i < xs.Length
        invariant 0 <= i <= xs.Length
        invariant 0 <= firstOccurIndex < i
        invariant xs[firstOccurIndex] == mostFreqValue
        invariant maxCount == CountOccurrences(xs[..], mostFreqValue)
        invariant forall k :: 0 <= k < i ==> CountOccurrences(xs[..], xs[k]) <= maxCount
        invariant forall k :: 0 <= k < firstOccurIndex ==> CountOccurrences(xs[..], xs[k]) < maxCount
    {
        var currentCount := CountOccurrences(xs[..], xs[i]);

        if currentCount > maxCount {
            maxCount := currentCount;
            mostFreqValue := xs[i];
            firstOccurIndex := i;
        } else if currentCount == maxCount && i < firstOccurIndex {
            // This case should ideally not happen if firstOccurIndex is tracked correctly
            // Since we are iterating from left to right, if xs[i] has the same maxCount
            // and its index 'i' is less than 'firstOccurIndex', it means 'firstOccurIndex' was set incorrectly.
            // A correct firstOccurIndex would be the leftmost one with max frequency.
            // This block is technically unreachable with correct firstOccurIndex management.
        }
        i := i + 1;
    }
    result := mostFreqValue;
}
// </vc-code>

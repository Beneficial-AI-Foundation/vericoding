// <vc-preamble>
/* Helper function to count occurrences of a target value in a sequence */
function CountOccurrences(xs: seq<int>, target: int): nat
{
    |set i | 0 <= i < |xs| && xs[i] == target|
}
// </vc-preamble>

// <vc-helpers>

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
    var mf_candidate := xs[0];
    var mf_count := CountOccurrences(xs[..], mf_candidate);

    var i := 1;
    while i < xs.Length
        invariant 1 <= i <= xs.Length
        invariant mf_candidate in xs[..]
        invariant mf_count == CountOccurrences(xs[..], mf_candidate)
        invariant forall k :: 0 <= k < i ==> CountOccurrences(xs[..], xs[k]) <= mf_count
        invariant exists first_idx :: 
            0 <= first_idx < i && 
            xs[first_idx] == mf_candidate && 
            (forall j :: 0 <= j < first_idx ==> CountOccurrences(xs[..], xs[j]) < mf_count)
    {
        var current_count := CountOccurrences(xs[..], xs[i]);
        if current_count > mf_count {
            mf_candidate := xs[i];
            mf_count := current_count;
        }
        i := i + 1;
    }

    result := mf_candidate;
}
// </vc-code>

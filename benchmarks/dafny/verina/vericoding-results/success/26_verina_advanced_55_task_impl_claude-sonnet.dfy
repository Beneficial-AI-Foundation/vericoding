// <vc-preamble>
/* Helper function to count occurrences of a target value in a sequence */
function CountOccurrences(xs: seq<int>, target: int): nat
{
    |set i | 0 <= i < |xs| && xs[i] == target|
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added invariant to track earliest occurrence */
function CountOccurrencesUpTo(xs: seq<int>, target: int, end: nat): nat
    requires end <= |xs|
{
    |set i | 0 <= i < end && xs[i] == target|
}

lemma CountOccurrencesUpToExtend(xs: seq<int>, target: int, end: nat)
    requires end < |xs|
    ensures CountOccurrencesUpTo(xs, target, end + 1) == CountOccurrencesUpTo(xs, target, end) + (if xs[end] == target then 1 else 0)
{
    var s1 := set i | 0 <= i < end && xs[i] == target;
    var s2 := set i | 0 <= i < end + 1 && xs[i] == target;
    if xs[end] == target {
        assert s2 == s1 + {end};
        assert end !in s1;
    } else {
        assert s2 == s1;
    }
}

lemma CountOccurrencesUpToComplete(xs: seq<int>, target: int)
    ensures CountOccurrencesUpTo(xs, target, |xs|) == CountOccurrences(xs, target)
{
}
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
    /* code modified by LLM (iteration 3): initialize maxCount with actual count of first element */
    var maxElement := xs[0];
    var maxFirstIdx := 0;
    
    // Calculate initial count for xs[0]
    var initialCount := 0;
    for j := 0 to xs.Length
        invariant 0 <= j <= xs.Length
        invariant initialCount == CountOccurrencesUpTo(xs[..], xs[0], j)
    {
        if xs[j] == xs[0] {
            initialCount := initialCount + 1;
        }
        if j < xs.Length {
            CountOccurrencesUpToExtend(xs[..], xs[0], j);
        }
    }
    CountOccurrencesUpToComplete(xs[..], xs[0]);
    var maxCount := initialCount;
    
    for i := 0 to xs.Length
        invariant 0 <= i <= xs.Length
        invariant maxElement in xs[..]
        invariant maxCount == CountOccurrences(xs[..], maxElement)
        invariant forall x :: x in xs[..i] ==> CountOccurrences(xs[..], x) <= maxCount
        invariant 0 <= maxFirstIdx < xs.Length && xs[maxFirstIdx] == maxElement
        invariant forall j :: 0 <= j < maxFirstIdx ==> CountOccurrences(xs[..], xs[j]) < maxCount
    {
        var currentCount := 0;
        for j := 0 to xs.Length
            invariant 0 <= j <= xs.Length
            invariant currentCount == CountOccurrencesUpTo(xs[..], xs[i], j)
        {
            if xs[j] == xs[i] {
                currentCount := currentCount + 1;
            }
            if j < xs.Length {
                CountOccurrencesUpToExtend(xs[..], xs[i], j);
            }
        }
        CountOccurrencesUpToComplete(xs[..], xs[i]);
        
        if currentCount > maxCount || (currentCount == maxCount && i < maxFirstIdx) {
            maxCount := currentCount;
            maxElement := xs[i];
            maxFirstIdx := i;
        }
    }
    
    result := maxElement;
}
// </vc-code>

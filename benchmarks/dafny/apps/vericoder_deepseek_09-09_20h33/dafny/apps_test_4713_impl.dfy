function MaxValue(S: string): int
{
    MaxValueUpToIndex(S, |S|)
}

function MaxValueUpToIndex(S: string, upTo: int): int
    requires 0 <= upTo <= |S|
{
    if upTo == 0 then 0
    else 
        var currentValue := CurrentValueAtIndex(S, upTo);
        var maxBefore := MaxValueUpToIndex(S, upTo - 1);
        if currentValue > maxBefore then currentValue else maxBefore
}

function CurrentValueAtIndex(S: string, index: int): int
    requires 0 <= index <= |S|
{
    if index == 0 then 0
    else CurrentValueAtIndex(S, index - 1) + (if S[index - 1] == 'I' then 1 else -1)
}

// <vc-helpers>
lemma MaxValueUpToIndexMonotonic(S: string, i: int, j: int)
    requires 0 <= i <= j <= |S|
    ensures MaxValueUpToIndex(S, i) <= MaxValueUpToIndex(S, j)
{
    if i < j {
        MaxValueUpToIndexMonotonic(S, i, j - 1);
    }
}

lemma CurrentValueAtIndexZero(S: string)
    ensures CurrentValueAtIndex(S, 0) == 0
{
}

lemma MaxValueUpToIndexZero(S: string)
    ensures MaxValueUpToIndex(S, 0) == 0
{
}
// </vc-helpers>

// <vc-spec>
method solve(N: int, S: string) returns (result: int)
    requires 1 <= N <= 100
    requires N == |S|
    requires forall i :: 0 <= i < |S| ==> S[i] == 'I' || S[i] == 'D'
    ensures result >= 0
    ensures result == MaxValue(S)
// </vc-spec>
// <vc-code>
{
    var currentMax := 0;
    var currentValue := 0;
    var i := 0;
    while i < N
        invariant 0 <= i <= N
        invariant currentValue == CurrentValueAtIndex(S, i)
        invariant currentMax == MaxValueUpToIndex(S, i)
    {
        if S[i] == 'I' {
            currentValue := currentValue + 1;
        } else {
            currentValue := currentValue - 1;
        }
        i := i + 1;
        if currentValue > currentMax {
            currentMax := currentValue;
        }
    }
    result := currentMax;
}
// </vc-code>


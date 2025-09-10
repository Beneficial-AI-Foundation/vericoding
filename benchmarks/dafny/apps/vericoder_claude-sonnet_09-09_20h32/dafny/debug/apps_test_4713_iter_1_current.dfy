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
lemma MaxValueNonNegative(S: string)
    requires forall i :: 0 <= i < |S| ==> S[i] == 'I' || S[i] == 'D'
    ensures MaxValue(S) >= 0
{
    MaxValueUpToIndexNonNegative(S, |S|);
}

lemma MaxValueUpToIndexNonNegative(S: string, upTo: int)
    requires 0 <= upTo <= |S|
    requires forall i :: 0 <= i < |S| ==> S[i] == 'I' || S[i] == 'D'
    ensures MaxValueUpToIndex(S, upTo) >= 0
{
    if upTo == 0 {
        // Base case: MaxValueUpToIndex(S, 0) == 0 >= 0
    } else {
        MaxValueUpToIndexNonNegative(S, upTo - 1);
        CurrentValueAtIndexProperties(S, upTo);
    }
}

lemma CurrentValueAtIndexProperties(S: string, index: int)
    requires 0 <= index <= |S|
    requires forall i :: 0 <= i < |S| ==> S[i] == 'I' || S[i] == 'D'
    ensures CurrentValueAtIndex(S, index) >= -index
{
    if index == 0 {
        // Base case
    } else {
        CurrentValueAtIndexProperties(S, index - 1);
    }
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
    var maxVal := 0;
    var currentVal := 0;
    
    for i := 0 to N
        invariant 0 <= i <= N
        invariant currentVal == CurrentValueAtIndex(S, i)
        invariant maxVal == MaxValueUpToIndex(S, i)
        invariant maxVal >= 0
    {
        if currentVal > maxVal {
            maxVal := currentVal;
        }
        
        if i < N {
            if S[i] == 'I' {
                currentVal := currentVal + 1;
            } else {
                currentVal := currentVal - 1;
            }
        }
    }
    
    result := maxVal;
}
// </vc-code>


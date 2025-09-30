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
lemma MaxValueUpToIndexCorrectness(S: string, upTo: int)
    requires 0 <= upTo <= |S|
    ensures MaxValueUpToIndex(S, upTo) >= 0
    ensures upTo == 0 ==> MaxValueUpToIndex(S, upTo) == 0
    ensures upTo > 0 ==> MaxValueUpToIndex(S, upTo) >= CurrentValueAtIndex(S, upTo)
    ensures upTo > 0 ==> MaxValueUpToIndex(S, upTo) >= MaxValueUpToIndex(S, upTo - 1)
{
    if upTo == 0 {
        // Base case: MaxValueUpToIndex(S, 0) == 0
    } else {
        MaxValueUpToIndexCorrectness(S, upTo - 1);
        var currentValue := CurrentValueAtIndex(S, upTo);
        var maxBefore := MaxValueUpToIndex(S, upTo - 1);
        assert MaxValueUpToIndex(S, upTo) == (if currentValue > maxBefore then currentValue else maxBefore);
    }
}

lemma CurrentValueRelation(S: string, index: int)
    requires 0 < index <= |S|
    requires forall i :: 0 <= i < |S| ==> S[i] == 'I' || S[i] == 'D'
    ensures CurrentValueAtIndex(S, index) == CurrentValueAtIndex(S, index - 1) + (if S[index - 1] == 'I' then 1 else -1)
{
    // This follows directly from the function definition
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
    var currentValue := 0;
    var maxValue := 0;
    var i := 0;
    
    while i < N
        invariant 0 <= i <= N
        invariant currentValue == CurrentValueAtIndex(S, i)
        invariant maxValue == MaxValueUpToIndex(S, i)
        invariant maxValue >= 0
    {
        MaxValueUpToIndexCorrectness(S, i);
        
        ghost var oldMaxValue := maxValue;
        
        if S[i] == 'I' {
            currentValue := currentValue + 1;
        } else {
            currentValue := currentValue - 1;
        }
        
        assert currentValue == CurrentValueAtIndex(S, i + 1) by {
            CurrentValueRelation(S, i + 1);
        }
        
        if currentValue > maxValue {
            maxValue := currentValue;
        }
        
        assert maxValue == MaxValueUpToIndex(S, i + 1) by {
            var cv := CurrentValueAtIndex(S, i + 1);
            var mb := MaxValueUpToIndex(S, i);
            assert cv == currentValue;
            assert mb == oldMaxValue;
            assert MaxValueUpToIndex(S, i + 1) == (if cv > mb then cv else mb);
        }
        
        i := i + 1;
    }
    
    result := maxValue;
}
// </vc-code>


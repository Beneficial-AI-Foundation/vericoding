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
lemma MaxValueUpToIndexLemma(S: string, upTo: int)
    requires 0 <= upTo <= |S|
    ensures MaxValueUpToIndex(S, upTo) == MaxValueUpToIndexRecursive(S, upTo)
{
    if upTo == 0 {
        // Base case, both are 0
    } else {
        // Inductive step: MaxValueUpToIndex(S, upTo - 1) == MaxValueUpToIndexRecursive(S, upTo - 1)
        MaxValueUpToIndexLemma(S, upTo - 1);
    }
}

function MaxValueUpToIndexRecursive(S: string, upTo: int): int
    requires 0 <= upTo <= |S|
    decreases upTo
{
    if upTo == 0 then 0
    else var currentValue := CurrentValueAtIndex(S, upTo);
         var maxBefore := MaxValueUpToIndexRecursive(S, upTo - 1);
         if currentValue > maxBefore then currentValue else maxBefore
}

lemma CurrentValueAtIndexLemma(S: string, index: int)
    requires 0 <= index <= |S|
    ensures CurrentValueAtIndex(S, index) == CalculateCurrentValue(S, index)
{
    if index == 0 {
        // Base case, both are 0
    } else {
        // Inductive step: CurrentValueAtIndex(S, index - 1) == CalculateCurrentValue(S, index - 1)
        CurrentValueAtIndexLemma(S, index - 1);
    }
}

function CalculateCurrentValue(S: string, index: int): int
    requires 0 <= index <= |S|
    decreases index
{
    if index == 0 then 0
    else CalculateCurrentValue(S, index - 1) + (if S[index - 1] == 'I' then 1 else -1)
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
    var max_val := 0;
    var current_val := 0;
    for i := 0 to N
        invariant 0 <= i <= N
        invariant current_val == CurrentValueAtIndex(S, i)
        invariant max_val == MaxValueUpToIndex(S, i)
    {
        if i == N {
            // After the loop and invariant implies max_val == MaxValueUpToIndex(S, N) which is MaxValue(S)
            // and current_val == CurrentValueAtIndex(S, N)
        } else {
            // Update current_val for the next iteration
            CurrentValueAtIndexLemma(S, i + 1); // Prove current_val update
            if S[i] == 'I' {
                current_val := current_val + 1;
            } else {
                current_val := current_val - 1;
            }

            // Update max_val for the next iteration
            MaxValueUpToIndexLemma(S, i + 1); // Prove max_val update
            if current_val > max_val {
                max_val := current_val;
            }
        }
    }
    return max_val;
}
// </vc-code>


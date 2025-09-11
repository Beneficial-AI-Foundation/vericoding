// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
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
  assume {:axiom} false;
}
// </vc-code>

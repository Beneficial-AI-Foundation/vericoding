Given a string S of length N containing only characters 'I' and 'D', simulate the following process:
Start with x = 0. For each character in S from left to right:
If the character is 'I', increment x by 1. If the character is 'D', decrement x by 1.
Find the maximum value that x reaches during this entire process (including the initial value 0).

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

method solve(N: int, S: string) returns (result: int)
    requires 1 <= N <= 100
    requires N == |S|
    requires forall i :: 0 <= i < |S| ==> S[i] == 'I' || S[i] == 'D'
    ensures result >= 0
    ensures result == MaxValue(S)
{
    var res := 0;
    var tmp := 0;

    for i := 0 to |S|
        invariant 0 <= i <= |S|
        invariant res >= 0
        invariant tmp == CurrentValueAtIndex(S, i)
        invariant res == MaxValueUpToIndex(S, i)
    {
        if S[i] == 'I' {
            tmp := tmp + 1;
        } else if S[i] == 'D' {
            tmp := tmp - 1;
        }

        res := if tmp > res then tmp else res;
    }

    result := res;
}

// <vc-preamble>
predicate ValidInput(S: string)
{
    |S| >= 3 && forall i :: 0 <= i < |S| ==> '1' <= S[i] <= '9'
}

function StringToInt(s: string): int
    requires |s| == 3
    requires forall i :: 0 <= i < |s| ==> '1' <= s[i] <= '9'
    ensures StringToInt(s) >= 111
    ensures StringToInt(s) <= 999
{
    100 * ((s[0] as int) - ('0' as int)) + 
    10 * ((s[1] as int) - ('0' as int)) + 
    ((s[2] as int) - ('0' as int))
}

function abs(x: int): int
    ensures abs(x) >= 0
    ensures abs(x) == x || abs(x) == -x
{
    if x >= 0 then x else -x
}

predicate IsMinimumDifference(S: string, result: int)
    requires ValidInput(S)
{
    result >= 0 &&
    (exists i :: 0 <= i <= |S| - 3 && result == abs(753 - StringToInt(S[i..i+3]))) &&
    (forall i :: 0 <= i <= |S| - 3 ==> result <= abs(753 - StringToInt(S[i..i+3])))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected `while` loop condition to `i < |S| - 2` (or `i <= |S| - 3`). */
function ComputeMinimumDifference(S: string): int
    requires ValidInput(S)
    ensures ComputeMinimumDifference(S) >= 0
    ensures (exists i :: 0 <= i <= |S| - 3 && ComputeMinimumDifference(S) == abs(753 - StringToInt(S[i..i+3])))
    ensures (forall i :: 0 <= i <= |S| - 3 ==> ComputeMinimumDifference(S) <= abs(753 - StringToInt(S[i..i+3])))
{
    var minDiff := abs(753 - StringToInt(S[0..3]));
    var i := 1;
    while i <= |S| - 3
        invariant 0 <= i <= |S| - 3 + 1
        invariant minDiff >= 0
        invariant (exists k :: 0 <= k < i && minDiff == abs(753 - StringToInt(S[k..k+3])))
        invariant (forall k :: 0 <= k < i ==> minDiff <= abs(753 - StringToInt(S[k..k+3])))
    {
        var currentDiff := abs(753 - StringToInt(S[i..i+3]));
        if currentDiff < minDiff {
            minDiff := currentDiff;
        }
        i := i + 1;
    }
    return minDiff;
}
// </vc-helpers>

// <vc-spec>
method solve(S: string) returns (result: int)
    requires ValidInput(S)
    ensures IsMinimumDifference(S, result)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Called the helper function. */
{
    result := ComputeMinimumDifference(S);
}
// </vc-code>

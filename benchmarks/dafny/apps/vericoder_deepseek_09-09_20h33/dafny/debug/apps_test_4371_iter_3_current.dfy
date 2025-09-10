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

// <vc-helpers>
lemma StringToIntSliceProperties(S: string, i: int)
    requires ValidInput(S)
    requires 0 <= i <= |S| - 3
    ensures |S[i..i+3]| == 3
    ensures forall j :: 0 <= j < 3 ==> '1' <= S[i..i+3][j] <= '9'
    ensures StringToInt(S[i..i+3]) >= 111
    ensures StringToInt(S[i..i+3]) <= 999
{
}

lemma AbsDifferenceProperties(x: int, y: int)
    ensures abs(x - y) >= 0
{
}

lemma MinimumDifferenceLemma(S: string, minDiff: int, i: int)
    requires ValidInput(S)
    requires 0 <= i <= |S| - 2
    requires minDiff >= 0
    requires forall j :: 0 <= j < i ==> minDiff <= abs(753 - StringToInt(S[j..j+3]))
    ensures exists j :: 0 <= j < i && (minDiff == abs(753 - StringToInt(S[j..j+3])) || minDiff <= abs(753 - StringToInt(S[j..j+3])))
{
}
// </vc-helpers>

// <vc-spec>
method solve(S: string) returns (result: int)
    requires ValidInput(S)
    ensures IsMinimumDifference(S, result)
// </vc-spec>
// <vc-code>
{
    var minDiff := 1000;
    var i := 0;
    while i <= |S| - 3
        invariant 0 <= i <= |S| - 2
        invariant minDiff >= 0
        invariant exists j :: 0 <= j < i && (minDiff == abs(753 - StringToInt(S[j..j+3])) || minDiff <= abs(753 - StringToInt(S[j..j+3])))
        invariant forall j :: 0 <= j < i ==> minDiff <= abs(753 - StringToInt(S[j..j+3]))
    {
        StringToIntSliceProperties(S, i);
        var currentNum := StringToInt(S[i..i+3]);
        var diff := abs(753 - currentNum);
        if diff < minDiff {
            minDiff := diff;
        }
        i := i + 1;
        MinimumDifferenceLemma(S, minDiff, i);
    }
    result := minDiff;
}
// </vc-code>


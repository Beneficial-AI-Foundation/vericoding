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
lemma StringToIntBounds(s: string, i: int)
    requires 0 <= i <= |s| - 3
    requires forall j :: 0 <= j < |s| ==> '1' <= s[j] <= '9'
    ensures forall k :: 0 <= k < 3 ==> '1' <= s[i+k] <= '9'
    ensures StringToInt(s[i..i+3]) >= 111
    ensures StringToInt(s[i..i+3]) <= 999
{
    assert forall k :: 0 <= k < 3 ==> i+k < |s|;
    assert forall k :: 0 <= k < 3 ==> '1' <= s[i+k] <= '9';
}

lemma SliceProperties(s: string, i: int)
    requires 0 <= i <= |s| - 3
    requires forall j :: 0 <= j < |s| ==> '1' <= s[j] <= '9'
    ensures |s[i..i+3]| == 3
    ensures forall k :: 0 <= k < 3 ==> '1' <= s[i..i+3][k] <= '9'
{
    assert s[i..i+3] == [s[i], s[i+1], s[i+2]];
}

lemma ExistsMinimumDifference(S: string, minDiff: int, i: int)
    requires ValidInput(S)
    requires 0 <= i <= |S| - 3
    requires minDiff >= 0
    requires forall j :: 0 <= j <= i ==> minDiff <= abs(753 - StringToInt(S[j..j+3]))
    ensures exists k :: 0 <= k <= i && minDiff == abs(753 - StringToInt(S[k..k+3]))
{
    assert minDiff <= abs(753 - StringToInt(S[0..3]));
    if minDiff == abs(753 - StringToInt(S[0..3])) {
        return;
    }
    
    var j := 1;
    while j <= i
        invariant 1 <= j <= i + 1
        invariant forall k :: 0 <= k < j ==> minDiff <= abs(753 - StringToInt(S[k..k+3]))
        invariant minDiff < abs(753 - StringToInt(S[0..3]))
    {
        if j <= i && minDiff == abs(753 - StringToInt(S[j..j+3])) {
            return;
        }
        j := j + 1;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(S: string) returns (result: int)
    requires ValidInput(S)
    ensures IsMinimumDifference(S, result)
// </vc-spec>
// <vc-code>
{
    SliceProperties(S, 0);
    StringToIntBounds(S, 0);
    
    var minDiff := abs(753 - StringToInt(S[0..3]));
    var i := 0;
    
    while i < |S| - 3
        invariant 0 <= i <= |S| - 3
        invariant minDiff >= 0
        invariant forall j :: 0 <= j <= i ==> minDiff <= abs(753 - StringToInt(S[j..j+3]))
        invariant exists j :: 0 <= j <= i && minDiff == abs(753 - StringToInt(S[j..j+3]))
    {
        i := i + 1;
        
        SliceProperties(S, i);
        StringToIntBounds(S, i);
        
        var currentDiff := abs(753 - StringToInt(S[i..i+3]));
        if currentDiff < minDiff {
            minDiff := currentDiff;
        }
    }
    
    ExistsMinimumDifference(S, minDiff, |S| - 3);
    result := minDiff;
}
// </vc-code>


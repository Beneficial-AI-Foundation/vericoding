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
lemma SubstringPreservesDigits(S: string, start: int)
    requires ValidInput(S)
    requires 0 <= start <= |S| - 3
    ensures |S[start..start+3]| == 3
    ensures forall i {:trigger S[start..start+3][i]} :: 0 <= i < 3 ==> '1' <= S[start..start+3][i] <= '9'
{
    assert |S[start..start+3]| == 3;
    forall i {:trigger S[start..start+3][i]} | 0 <= i < 3
        ensures '1' <= S[start..start+3][i] <= '9'
    {
        assert S[start..start+3][i] == S[start + i];
        assert 0 <= start + i < |S|;
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
    SubstringPreservesDigits(S, 0);
    result := abs(753 - StringToInt(S[0..3]));
    var k := 1;
    
    while k <= |S| - 3
        invariant 1 <= k <= |S| - 2
        invariant result >= 0
        invariant exists i {:trigger StringToInt(S[i..i+3])} :: 0 <= i <= k - 1 && result == abs(753 - StringToInt(S[i..i+3]))
        invariant forall i {:trigger StringToInt(S[i..i+3])} :: 0 <= i <= k - 1 ==> result <= abs(753 - StringToInt(S[i..i+3]))
    {
        SubstringPreservesDigits(S, k);
        var current := abs(753 - StringToInt(S[k..k+3]));
        if current < result {
            result := current;
        }
        k := k + 1;
    }
    
    assert exists i {:trigger StringToInt(S[i..i+3])} :: 0 <= i <= |S| - 3 && result == abs(753 - StringToInt(S[i..i+3]));
    assert forall i {:trigger StringToInt(S[i..i+3])} :: 0 <= i <= |S| - 3 ==> result <= abs(753 - StringToInt(S[i..i+3]));
}
// </vc-code>


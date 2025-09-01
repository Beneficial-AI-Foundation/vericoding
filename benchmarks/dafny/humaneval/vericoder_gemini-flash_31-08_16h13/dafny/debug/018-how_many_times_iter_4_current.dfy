

// <vc-helpers>
lemma SubstringLengthZeroMatchesAnywhere(s: string, substr: string, i: int)
    requires |substr| == 0
    requires 0 <= i <= |s|
    ensures s[i .. i + |substr|] == substr
{
}
// </vc-helpers>

// <vc-spec>
method how_many_times(s: string, substr: string) returns (times: int)
    // post-condition-start
    ensures times == |set i {:trigger} | 0 <= i <= |s| - |substr| && s[i..i+|substr|] == substr|
    // post-condition-end
// </vc-spec>
// <vc-code>
{
    var count := 0;
    var i := 0;
    if |substr| == 0 {
        return |s| + 1;
    }
    while i <= |s| - |substr|
        invariant 0 <= i <= |s|
        invariant 0 <= i <= |s| - |substr| + 1
        invariant count == |set k {:trigger} | 0 <= k < i && k + |substr| <= |s| && s[k..k+|substr|] == substr|
    {
        if s[i..i+|substr|] == substr {
            count := count + 1;
        }
        i := i + 1;
    }
    times := count;
}
// </vc-code>


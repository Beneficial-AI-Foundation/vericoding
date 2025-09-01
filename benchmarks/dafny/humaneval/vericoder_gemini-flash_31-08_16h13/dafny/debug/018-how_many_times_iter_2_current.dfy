

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
    while i <= |s| // Loop until i goes beyond the string length
        invariant 0 <= i <= |s| + 1
        invariant count == |set k {:trigger} | 0 <= k < i && k <= |s| - |substr| && s[k..k+|substr|] == substr|
        // If substr is empty, count should always be |s| + 1 eventually
        invariant |substr| != 0 || count == i
    {
        if |substr| == 0 {
            count := |s| + 1; // It matches before each character and at the end
            break;
        }

        if i + |substr| <= |s| && s[i..i+|substr|] == substr {
            count := count + 1;
        }
        i := i + 1;
    }
    times := count;
    if |substr| == 0 {
        assert times == |s| + 1;
        assert |set p {:trigger} | 0 <= p <= |s| - |substr| && s[p..p+|substr|] == substr| == |set p | 0 <= p <= |s| && true |;
        assert |set p | 0 <= p <= |s| && true | == |s| + 1;
    }
}
// </vc-code>


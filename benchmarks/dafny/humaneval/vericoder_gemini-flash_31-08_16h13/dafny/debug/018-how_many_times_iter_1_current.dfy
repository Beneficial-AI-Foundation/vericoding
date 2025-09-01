

// <vc-helpers>

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
    while i <= |s| - |substr|
        invariant 0 <= i <= |s| - |substr| + 1
        invariant count == |set k {:trigger} | 0 <= k < i && k <= |s| - |substr| && s[k..k+|substr|] == substr|
    {
        if |substr| == 0 { // Special case: a zero-length substring always matches
            count := |s| + 1; // It matches before each character and at the end
            break;
        }
        if i + |substr| <= |s| && s[i..i+|substr|] == substr {
            count := count + 1;
        }
        i := i + 1;
    }
    times := count;
}
// </vc-code>


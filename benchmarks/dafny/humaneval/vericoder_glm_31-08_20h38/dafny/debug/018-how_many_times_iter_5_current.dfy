

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
    if |substr| == 0 {
        return |s| + 1;
    }
    if |substr| > |s| {
        return 0;
    }
    var count := 0;
    ghost var found: set<int> := {};
    var i := 0;
    while i <= |s| - |substr|
        invariant 0 <= i <= |s| - |substr| + 1
        invariant found == { j {:trigger} | 0 <= j < i && s[j..j+|substr|] == substr }
        invariant count == |found|
    {
        if s[i..i+|substr|] == substr {
            found := found union {i};
            count := count + 1;
        }
        i := i + 1;
    }
    return count;
}
// </vc-code>


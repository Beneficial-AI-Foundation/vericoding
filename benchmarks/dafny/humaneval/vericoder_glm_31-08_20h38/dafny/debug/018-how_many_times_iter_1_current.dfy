

// <vc-helpers>
lemma lemma_string_slice(s: string, i: int, j: int)
    requires 0 <= i <= j <= |s|
    ensures |s[i..j]| == j - i
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
    times := 0;
    var substr_len := |substr|;
    if substr_len == 0 {
        times := |s| + 1;
        return;
    }
    
    var i := 0;
    while i <= |s| - substr_len
        invariant 0 <= i <= |s| - substr_len + 1
        invariant times == |set j | 0 <= j < i && s[j..j+substr_len] == substr|
    {
        if s[i..i+substr_len] == substr {
            times := times + 1;
        }
        i := i + 1;
    }
}
// </vc-code>


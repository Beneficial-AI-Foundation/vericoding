

// <vc-helpers>
lemma lemma_string_slice(s: string, i: int, j: int)
    requires 0 <= i <= j <= |s|
// </vc-helpers>

// <vc-spec>
method how_many_times(s: string, substr: string) returns (times: int)
    // post-condition-start
    ensures times == |set i {:trigger} | 0 <= i <= |s| - |substr| && s[i..i+|substr|] == substr|
    // post-condition-end
// </vc-spec>
// <vc-code>
lemma lemma_string_slice(s: string, i: int, j: int)
    requires 0 <= i <= j <= |s|
// </vc-code>


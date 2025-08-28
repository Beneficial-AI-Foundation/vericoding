method how_many_times(s: string, substr: string) returns (times: int)
    // post-condition-start
    ensures times == |set i {:trigger} | 0 <= i <= |s| - |substr| && s[i..i+|substr|] == substr|
    // post-condition-end
{
    // impl-start
    times := 0;
    if (|substr| > |s|) {
        return;
    }
    ghost var starts: set<int> := {};
    for i := 0 to |s| - |substr| + 1
        // invariants-start
        invariant forall j :: j in starts ==> j < i
        invariant |starts| == times
        invariant starts == set j {:trigger} | 0 <= j < i && s[j..j+|substr|] == substr
        // invariants-end
    {
        if s[i..i+|substr|] == substr {
            times := times + 1;
            starts := starts + {i};
        }
    }
    assert starts == set i {:trigger} | 0 <= i <= |s| - |substr| && s[i..i+|substr|] == substr; // assert-line
    // impl-end
}

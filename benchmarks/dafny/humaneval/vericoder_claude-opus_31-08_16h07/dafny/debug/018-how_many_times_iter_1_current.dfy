

// <vc-helpers>
lemma SetCardinalityBound(s: string, substr: string, k: int)
    requires 0 <= k <= |s| - |substr| + 1
    ensures |set i | 0 <= i < k && s[i..i+|substr|] == substr| <= k
{
    var positions := set i | 0 <= i < k && s[i..i+|substr|] == substr;
    var range := set i | 0 <= i < k;
    assert positions <= range;
    assert |range| == k;
}

lemma ExtendSet(s: string, substr: string, k: int)
    requires 0 <= k < |s| - |substr| + 1
    ensures set i | 0 <= i <= k && s[i..i+|substr|] == substr == 
            (set i | 0 <= i < k && s[i..i+|substr|] == substr) + 
            (if s[k..k+|substr|] == substr then {k} else {})
{
    var S1 := set i | 0 <= i <= k && s[i..i+|substr|] == substr;
    var S2 := set i | 0 <= i < k && s[i..i+|substr|] == substr;
    var S3 := if s[k..k+|substr|] == substr then {k} else {};
    
    forall x | x in S1
    ensures x in S2 + S3
    {
        if x == k {
            assert s[k..k+|substr|] == substr;
            assert x in S3;
        } else {
            assert 0 <= x < k;
            assert x in S2;
        }
    }
    
    forall x | x in S2 + S3
    ensures x in S1
    {
        if x in S2 {
            assert 0 <= x < k;
            assert s[x..x+|substr|] == substr;
            assert x in S1;
        } else {
            assert x in S3;
            assert x == k;
            assert s[k..k+|substr|] == substr;
            assert x in S1;
        }
    }
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
    if |substr| == 0 || |substr| > |s| {
        return;
    }
    
    var i := 0;
    while i <= |s| - |substr|
        invariant 0 <= i <= |s| - |substr| + 1
        invariant times == |set j | 0 <= j < i && s[j..j+|substr|] == substr|
    {
        if s[i..i+|substr|] == substr {
            times := times + 1;
        }
        ExtendSet(s, substr, i);
        i := i + 1;
    }
    
    assert i == |s| - |substr| + 1;
    assert set j | 0 <= j < i && s[j..j+|substr|] == substr == 
           set j | 0 <= j <= |s| - |substr| && s[j..j+|substr|] == substr;
}
// </vc-code>


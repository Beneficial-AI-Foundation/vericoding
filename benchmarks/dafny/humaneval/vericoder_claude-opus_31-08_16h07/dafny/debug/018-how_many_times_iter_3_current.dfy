

// <vc-helpers>
lemma SetCardinalityBound(s: string, substr: string, k: int)
    requires 0 <= k <= |s| - |substr| + 1
    ensures |set i {:trigger} | 0 <= i < k && s[i..i+|substr|] == substr| <= k
{
    var positions := set i {:trigger} | 0 <= i < k && s[i..i+|substr|] == substr;
    var range := set i {:trigger} | 0 <= i < k;
    
    // Prove that positions is a subset of range
    forall x | x in positions
    ensures x in range
    {
        assert 0 <= x < k;
    }
    assert positions <= range;
    
    // The cardinality of range is k
    var f := (i: int) requires 0 <= i < k => i;
    assert forall i :: 0 <= i < k ==> f(i) in range;
    assert forall x :: x in range ==> 0 <= x < k && f(x) == x;
    
    // Since positions is a subset of range, its cardinality is at most k
    assert |positions| <= |range|;
}

lemma ExtendSet(s: string, substr: string, k: int)
    requires 0 <= k < |s| - |substr| + 1
    ensures (set i {:trigger} | 0 <= i <= k && s[i..i+|substr|] == substr) == 
            (set i {:trigger} | 0 <= i < k && s[i..i+|substr|] == substr) + 
            (if s[k..k+|substr|] == substr then {k} else {})
{
    var S1 := set i {:trigger} | 0 <= i <= k && s[i..i+|substr|] == substr;
    var S2 := set i {:trigger} | 0 <= i < k && s[i..i+|substr|] == substr;
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
    
    assert S1 == S2 + S3;
}

lemma EmptyOrTooLongSubstr(s: string, substr: string)
    requires |substr| == 0 || |substr| > |s|
    ensures |set i {:trigger} | 0 <= i <= |s| - |substr| && s[i..i+|substr|] == substr| == 0
{
    if |substr| == 0 {
        assert |s| - |substr| == |s|;
        // For empty substring, we can't have any valid positions
        assert forall i :: 0 <= i <= |s| ==> i + |substr| == i;
    } else {
        assert |substr| > |s|;
        assert |s| - |substr| < 0;
        var S := set i {:trigger} | 0 <= i <= |s| - |substr| && s[i..i+|substr|] == substr;
        assert forall i :: i in S ==> false;
        assert S == {};
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
        EmptyOrTooLongSubstr(s, substr);
        return;
    }
    
    var i := 0;
    ghost var seen := set j {:trigger} | 0 <= j < i && s[j..j+|substr|] == substr;
    
    while i <= |s| - |substr|
        invariant 0 <= i <= |s| - |substr| + 1
        invariant seen == set j {:trigger} | 0 <= j < i && s[j..j+|substr|] == substr
        invariant times == |seen|
    {
        ghost var old_seen := seen;
        
        if s[i..i+|substr|] == substr {
            times := times + 1;
            seen := seen + {i};
        }
        
        ExtendSet(s, substr, i);
        i := i + 1;
        seen := set j {:trigger} | 0 <= j < i && s[j..j+|substr|] == substr;
        
        assert seen == old_seen + (if s[i-1..i-1+|substr|] == substr then {i-1} else {});
    }
    
    assert i == |s| - |substr| + 1;
    assert seen == set j {:trigger} | 0 <= j < i && s[j..j+|substr|] == substr;
    assert seen == set j {:trigger} | 0 <= j <= |s| - |substr| && s[j..j+|substr|] == substr;
}
// </vc-code>


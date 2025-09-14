

// <vc-helpers>
lemma SetCardinalityBound(s: string, substr: string, k: int)
    requires 0 <= k <= |s| - |substr| + 1
    ensures |set i | 0 <= i < k && s[i..i+|substr|] == substr| <= k
{
    var positions := set i | 0 <= i < k && s[i..i+|substr|] == substr;
    var range := set i | 0 <= i < k;
    
    // Prove that positions is a subset of range
    forall x | x in positions
    ensures x in range
    {
        // x in positions means 0 <= x < k && s[x..x+|substr|] == substr
        // which implies 0 <= x < k, so x in range
    }
    
    // Since positions is a subset of range and |range| == k
    CardinalityOfIota(k);
    SubsetCardinality(positions, range);
}

lemma CardinalityOfIota(n: nat)
    ensures |set i | 0 <= i < n| == n
{
    if n == 0 {
        assert set i | 0 <= i < 0 == {};
    } else {
        CardinalityOfIota(n - 1);
        assert set i | 0 <= i < n == set i | 0 <= i < n - 1 :: i + {n - 1};
    }
}

lemma SubsetCardinality<T>(A: set<T>, B: set<T>)
    requires A <= B
    ensures |A| <= |B|
{
    if A == {} {
        assert |A| == 0 <= |B|;
    } else {
        var x :| x in A;
        SubsetCardinality(A - {x}, B - {x});
    }
}

lemma ExtendSet(s: string, substr: string, k: int)
    requires 0 <= k < |s| - |substr| + 1
    ensures (set i | 0 <= i <= k && s[i..i+|substr|] == substr) == 
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
            if s[k..k+|substr|] == substr {
                assert x in S3;
            }
        } else {
            assert 0 <= x < k && s[x..x+|substr|] == substr;
            assert x in S2;
        }
    }
    
    forall x | x in S2 + S3
    ensures x in S1
    {
        if x in S2 {
            assert 0 <= x < k && s[x..x+|substr|] == substr;
            assert 0 <= x <= k;
            assert x in S1;
        } else {
            assert x in S3;
            if s[k..k+|substr|] == substr {
                assert S3 == {k};
                assert x == k;
                assert 0 <= k <= k && s[k..k+|substr|] == substr;
                assert x in S1;
            } else {
                assert S3 == {};
                assert false;
            }
        }
    }
}

lemma EmptyOrTooLongSubstr(s: string, substr: string)
    requires |substr| == 0 || |substr| > |s|
    ensures |set i | 0 <= i <= |s| - |substr| && s[i..i+|substr|] == substr| == 0
{
    if |substr| == 0 {
        assert |s| - |substr| == |s|;
        var S := set i | 0 <= i <= |s| - |substr| && s[i..i+|substr|] == substr;
        assert S == set i | 0 <= i <= |s| && s[i..i] == substr;
        forall i | 0 <= i <= |s|
        ensures s[i..i] != substr
        {
            assert |s[i..i]| == 0;
            assert |substr| == 0;
            assert substr == "";
            assert s[i..i] == "";
        }
    } else {
        assert |substr| > |s|;
        assert |s| - |substr| < 0;
        var S := set i | 0 <= i <= |s| - |substr| && s[i..i+|substr|] == substr;
        forall i 
        ensures i !in S
        {
            if 0 <= i <= |s| - |substr| {
                assert |s| - |substr| < 0;
                assert false;
            }
        }
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
    ghost var seen := set j | 0 <= j < i && s[j..j+|substr|] == substr;
    
    while i <= |s| - |substr|
        invariant 0 <= i <= |s| - |substr| + 1
        invariant seen == set j | 0 <= j < i && s[j..j+|substr|] == substr
        invariant times == |seen|
    {
        ghost var old_seen := seen;
        ghost var old_i := i;
        
        if s[i..i+|substr|] == substr {
            ExtendSet(s, substr, i);
            seen := seen + {i};
            assert seen == set j | 0 <= j <= i && s[j..j+|substr|] == substr;
            times := times + 1;
        }
        
        i := i + 1;
        seen := set j | 0 <= j < i && s[j..j+|substr|] == substr;
        
        if s[old_i..old_i+|substr|] == substr {
            assert seen == old_seen + {old_i};
        } else {
            assert seen == old_seen;
        }
    }
    
    assert i == |s| - |substr| + 1;
    assert seen == set j | 0 <= j < |s| - |substr| + 1 && s[j..j+|substr|] == substr;
    assert seen == set j | 0 <= j <= |s| - |substr| && s[j..j+|substr|] == substr;
}
// </vc-code>




// <vc-helpers>
lemma SetCardinalityBound(s: set<int>, n: int)
    requires forall x :: x in s ==> 0 <= x < n
    requires n >= 0
    ensures |s| <= n
    decreases n
{
    if n == 0 {
        assert s == {};
    } else {
        var s' := set x | x in s && x < n - 1;
        assert forall x :: x in s' ==> 0 <= x < n - 1;
        SetCardinalityBound(s', n - 1);
        assert |s'| <= n - 1;
        
        if (n - 1) in s {
            assert s == s' + {n - 1};
            assert |s| == |s'| + 1;
            assert |s| <= n;
        } else {
            assert s == s';
            assert |s| == |s'|;
            assert |s| <= n - 1;
            assert |s| <= n;
        }
    }
}

lemma SetComprehensionSize(a: seq<int>, b: seq<int>, c: seq<int>, k: int)
    requires |a| == |b| == |c|
    requires 0 <= k <= |a|
    ensures |set i: int | 0 <= i < k && a[i] == b[i] && b[i] == c[i]| <= k
{
    var s := set i: int | 0 <= i < k && a[i] == b[i] && b[i] == c[i];
    assert forall x :: x in s ==> 0 <= x < k;
    if k >= 0 {
        SetCardinalityBound(s, k);
    }
}
// </vc-helpers>

// <vc-spec>
method CountIdenticalPositions(a: seq<int>, b: seq<int>, c: seq<int>) returns (count: int)
    requires |a| == |b| && |b| == |c|
    ensures count >= 0
    ensures count == | set i: int | 0 <= i < |a| && a[i] == b[i] && b[i] == c[i]|
// </vc-spec>
// <vc-code>
{
    count := 0;
    var k := 0;
    var seen := {};
    
    while k < |a|
        invariant 0 <= k <= |a|
        invariant seen == set i: int | 0 <= i < k && a[i] == b[i] && b[i] == c[i]
        invariant count == |seen|
    {
        if a[k] == b[k] && b[k] == c[k] {
            seen := seen + {k};
            count := count + 1;
        }
        k := k + 1;
    }
    
    assert seen == set i: int | 0 <= i < |a| && a[i] == b[i] && b[i] == c[i];
}
// </vc-code>


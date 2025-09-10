predicate ValidInput(n: int, aa: seq<int>)
{
    n >= 2 &&
    |aa| == n - 1 &&
    forall i :: 0 <= i < |aa| ==> 1 <= aa[i] < i + 2
}

function SubordinateCount(aa: seq<int>, boss_id: int): int
{
    |set j | 0 <= j < |aa| && aa[j] == boss_id|
}

predicate ValidOutput(n: int, aa: seq<int>, result: seq<int>)
{
    |result| == n &&
    forall i :: 0 <= i < n ==> result[i] >= 0 &&
    forall i :: 0 <= i < n ==> result[i] == SubordinateCount(aa, i + 1)
}

// <vc-helpers>
lemma SubordinateCountDefinition(aa: seq<int>, boss_id: int, count: int)
    ensures SubordinateCount(aa, boss_id) == count <==> 
            |set j | 0 <= j < |aa| && aa[j] == boss_id| == count
{
}

lemma SubsetCardinalityBound<T>(s: set<T>, all: set<T>)
    requires s <= all
    ensures |s| <= |all|
{
    if s == {} {
        assert |s| == 0;
    } else if s == all {
        assert |s| == |all|;
    } else {
        var x :| x in all && x !in s;
        var all' := all - {x};
        assert s <= all';
        SubsetCardinalityBound(s, all');
        assert |all| == |all'| + 1;
    }
}

lemma IndexSetCardinality(n: int)
    requires n >= 0
    ensures |set j {:trigger j >= 0} | 0 <= j < n| == n
{
    if n == 0 {
        assert (set j {:trigger j >= 0} | 0 <= j < 0) == {};
    } else {
        var prevSet := set j {:trigger j >= 0} | 0 <= j < n - 1;
        var currSet := set j {:trigger j >= 0} | 0 <= j < n;
        IndexSetCardinality(n - 1);
        assert |prevSet| == n - 1;
        assert currSet == prevSet + {n - 1};
        assert n - 1 !in prevSet;
        assert |currSet| == |prevSet| + 1;
        assert |currSet| == n;
    }
}

lemma SubordinateCountBounds(aa: seq<int>, boss_id: int)
    ensures 0 <= SubordinateCount(aa, boss_id) <= |aa|
{
    var s := set j | 0 <= j < |aa| && aa[j] == boss_id;
    var all := set j {:trigger j >= 0} | 0 <= j < |aa|;
    
    // Prove s <= all
    forall x | x in s
        ensures x in all
    {
        assert 0 <= x < |aa| && aa[x] == boss_id;
        assert 0 <= x < |aa|;
    }
    assert s <= all;
    
    SubsetCardinalityBound(s, all);
    assert |s| <= |all|;
    
    IndexSetCardinality(|aa|);
    assert |all| == |aa|;
    
    assert |s| <= |aa|;
    assert SubordinateCount(aa, boss_id) == |s|;
}

lemma SetSizeIncrement(aa: seq<int>, k: int, boss_id: int, prevSet: set<int>)
    requires 0 <= k < |aa|
    requires prevSet == set j | 0 <= j < k && aa[j] == boss_id
    ensures aa[k] == boss_id ==> 
        (set j | 0 <= j < k + 1 && aa[j] == boss_id) == prevSet + {k}
    ensures aa[k] != boss_id ==> 
        (set j | 0 <= j < k + 1 && aa[j] == boss_id) == prevSet
{
    var nextSet := set j | 0 <= j < k + 1 && aa[j] == boss_id;
    if aa[k] == boss_id {
        assert k in nextSet;
        assert nextSet == prevSet + {k};
    } else {
        assert k !in nextSet;
        forall j | j in nextSet
            ensures j in prevSet
        {
            assert 0 <= j < k + 1 && aa[j] == boss_id;
            if j == k {
                assert aa[j] == boss_id;
                assert aa[k] != boss_id;
                assert false;
            }
            assert j < k;
        }
        forall j | j in prevSet
            ensures j in nextSet
        {
            assert 0 <= j < k && aa[j] == boss_id;
            assert j < k + 1;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, aa: seq<int>) returns (result: seq<int>)
    requires ValidInput(n, aa)
    ensures ValidOutput(n, aa, result)
// </vc-spec>
// <vc-code>
{
    result := [];
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] >= 0
        invariant forall j :: 0 <= j < i ==> result[j] == SubordinateCount(aa, j + 1)
    {
        var count := 0;
        var k := 0;
        ghost var currentSet := set j | 0 <= j < 0 && aa[j] == i + 1;
        assert currentSet == {};
        
        while k < |aa|
            invariant 0 <= k <= |aa|
            invariant currentSet == set j | 0 <= j < k && aa[j] == i + 1
            invariant count == |currentSet|
        {
            ghost var prevSet := currentSet;
            currentSet := set j | 0 <= j < k + 1 && aa[j] == i + 1;
            
            if aa[k] == i + 1 {
                SetSizeIncrement(aa, k, i + 1, prevSet);
                assert currentSet == prevSet + {k};
                assert k !in prevSet;
                count := count + 1;
            } else {
                SetSizeIncrement(aa, k, i + 1, prevSet);
                assert currentSet == prevSet;
            }
            k := k + 1;
        }
        
        assert currentSet == set j | 0 <= j < |aa| && aa[j] == i + 1;
        assert count == |currentSet|;
        assert count == SubordinateCount(aa, i + 1);
        SubordinateCountBounds(aa, i + 1);
        
        result := result + [count];
        i := i + 1;
    }
}
// </vc-code>


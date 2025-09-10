predicate ValidInput(arr: seq<int>) {
    true // No specific constraints on input beyond being a sequence of integers
}

function DistinctNonZeroCount(arr: seq<int>): int {
    |set x | x in arr && x != 0|
}

// <vc-helpers>
lemma DistinctNonZeroCountBounds(arr: seq<int>)
    ensures DistinctNonZeroCount(arr) >= 0
    ensures DistinctNonZeroCount(arr) <= |arr|
{
    var s := set x | x in arr && x != 0;
    assert s <= set x | x in arr;
    SetSubsetCardinality(s, set x | x in arr);
    SeqToSetCardinality(arr);
}

lemma SetSubsetCardinality<T>(s1: set<T>, s2: set<T>)
    requires s1 <= s2
    ensures |s1| <= |s2|
{
    if s1 == {} {
        assert |s1| == 0;
        assert |s1| <= |s2|;
    } else if s1 == s2 {
        assert |s1| == |s2|;
    } else {
        var x :| x in s1;
        var s1' := s1 - {x};
        var s2' := s2 - {x};
        assert s1' < s1;
        assert s1' <= s2';
        assert s2' <= s2;
        SetSubsetCardinality(s1', s2');
        assert |s1'| <= |s2'|;
        assert |s1| == |s1'| + 1;
        if x in s2 {
            assert |s2| == |s2'| + 1;
            assert |s1| <= |s2|;
        } else {
            assert false; // contradiction since s1 <= s2 and x in s1
        }
    }
}

lemma SeqToSetCardinality<T>(arr: seq<T>)
    ensures |set x | x in arr| <= |arr|
{
    if |arr| == 0 {
        assert arr == [];
        var emptySet := set x | x in arr;
        assert emptySet == {};
    } else {
        var head := arr[0];
        var tail := arr[1..];
        var headSet := {head};
        var tailSet := set x | x in tail;
        var fullSet := set x | x in arr;
        
        assert forall x :: x in fullSet ==> x == head || x in tailSet;
        assert fullSet <= headSet + tailSet;
        assert |headSet| == 1;
        
        SeqToSetCardinality(tail);
        assert |tailSet| <= |tail|;
        assert |tail| == |arr| - 1;
        
        SetUnionCardinality(headSet, tailSet);
        assert |headSet + tailSet| <= |headSet| + |tailSet|;
        assert |fullSet| <= |headSet + tailSet|;
        assert |fullSet| <= 1 + |tail|;
        assert 1 + |tail| == |arr|;
    }
}

lemma SetUnionCardinality<T>(s1: set<T>, s2: set<T>)
    ensures |s1 + s2| <= |s1| + |s2|
{
    if s1 == {} {
        assert s1 + s2 == s2;
        assert |s1 + s2| == |s2|;
        assert |s1| == 0;
        assert |s1 + s2| <= |s1| + |s2|;
    } else {
        var x :| x in s1;
        var s1' := s1 - {x};
        assert s1 == s1' + {x};
        assert |s1| == |s1'| + 1;
        
        if x in s2 {
            assert s1 + s2 == s1' + s2;
            SetUnionCardinality(s1', s2);
            assert |s1 + s2| <= |s1'| + |s2|;
            assert |s1 + s2| <= |s1| - 1 + |s2|;
            assert |s1 + s2| < |s1| + |s2|;
        } else {
            assert s1 + s2 == s1' + s2 + {x};
            SetUnionCardinality(s1', s2);
            assert |s1' + s2| <= |s1'| + |s2|;
            assert |s1 + s2| == |s1' + s2| + 1;
            assert |s1 + s2| <= |s1'| + |s2| + 1;
            assert |s1 + s2| <= |s1| + |s2|;
        }
    }
}

lemma NonZeroSetSize(seen: set<int>, arr: seq<int>, i: int)
    requires 0 <= i <= |arr|
    requires seen == set x | x in arr[..i] && x != 0
    ensures |seen| <= i
{
    var allSeen := set x | x in arr[..i];
    assert seen <= allSeen;
    SetSubsetCardinality(seen, allSeen);
    SeqToSetCardinality(arr[..i]);
    assert |arr[..i]| == i;
}
// </vc-helpers>

// <vc-spec>
method solve(arr: seq<int>) returns (result: int)
    requires ValidInput(arr)
    ensures result >= 0
    ensures result <= |arr|
    ensures result == DistinctNonZeroCount(arr)
// </vc-spec>
// <vc-code>
{
    var seen: set<int> := {};
    var count := 0;
    var i := 0;
    
    while i < |arr|
        invariant 0 <= i <= |arr|
        invariant seen == set x | x in arr[..i] && x != 0
        invariant count == |seen|
        invariant count >= 0
        invariant count <= i
    {
        if arr[i] != 0 && arr[i] !in seen {
            seen := seen + {arr[i]};
            count := count + 1;
        }
        i := i + 1;
        
        NonZeroSetSize(seen, arr, i);
    }
    
    assert arr[..i] == arr;
    assert seen == set x | x in arr && x != 0;
    assert count == |seen|;
    assert count == DistinctNonZeroCount(arr);
    DistinctNonZeroCountBounds(arr);
    result := count;
}
// </vc-code>


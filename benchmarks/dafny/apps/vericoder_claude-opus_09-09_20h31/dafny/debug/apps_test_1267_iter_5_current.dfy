predicate ValidInput(n: int, scores: seq<int>)
{
    n == |scores| && n >= 1 && exists i :: 0 <= i < |scores| && scores[i] != 0
}

function UniqueNonZeroScores(scores: seq<int>): set<int>
{
    set i | 0 <= i < |scores| && scores[i] != 0 :: scores[i]
}

predicate ValidResult(scores: seq<int>, result: int)
{
    result >= 1 && 
    result == |UniqueNonZeroScores(scores)| && 
    result <= |scores|
}

// <vc-helpers>
lemma UniqueNonZeroScoresSubset(scores: seq<int>, i: int, seen: set<int>)
    requires 0 <= i <= |scores|
    requires seen == set j | 0 <= j < i && scores[j] != 0 :: scores[j]
    ensures seen <= UniqueNonZeroScores(scores)
    decreases |scores| - i
{
    if i < |scores| {
        var seen' := if scores[i] != 0 then seen + {scores[i]} else seen;
        assert seen' == set j | 0 <= j < i + 1 && scores[j] != 0 :: scores[j];
        UniqueNonZeroScoresSubset(scores, i + 1, seen');
    }
}

lemma UniqueNonZeroScoresComplete(scores: seq<int>, seen: set<int>)
    requires seen == set j | 0 <= j < |scores| && scores[j] != 0 :: scores[j]
    ensures seen == UniqueNonZeroScores(scores)
{
}

lemma UniqueNonZeroScoresBounded(scores: seq<int>)
    ensures |UniqueNonZeroScores(scores)| <= |scores|
{
    var values := UniqueNonZeroScores(scores);
    var indices := set i | 0 <= i < |scores| && scores[i] != 0;
    
    // Create a mapping from each value to one of its indices
    var valueToIndex := map v | v in values :: 
        var i :| 0 <= i < |scores| && scores[i] != 0 && scores[i] == v; i;
    
    // The mapping is injective from values to indices
    forall v1, v2 | v1 in values && v2 in values && v1 != v2
        ensures valueToIndex[v1] != valueToIndex[v2]
    {
        var i1 := valueToIndex[v1];
        var i2 := valueToIndex[v2];
        assert scores[i1] == v1;
        assert scores[i2] == v2;
        if i1 == i2 {
            assert scores[i1] == scores[i2];
            assert v1 == v2;
            assert false;
        }
    }
    
    // Since we have an injective mapping from values to indices
    // and indices is a subset of 0..|scores|, we have |values| <= |indices| <= |scores|
    assert forall v | v in values :: valueToIndex[v] in indices;
    InjectiveMappingCardinality(values, indices, valueToIndex);
    assert |indices| <= |scores|;
}

lemma InjectiveMappingCardinality<T,U>(s: set<T>, t: set<U>, f: map<T,U>)
    requires forall x | x in s :: x in f && f[x] in t
    requires forall x1, x2 | x1 in s && x2 in s && x1 != x2 :: f[x1] != f[x2]
    ensures |s| <= |t|
{
    if s == {} {
        assert |s| == 0 <= |t|;
    } else {
        var x :| x in s;
        var s' := s - {x};
        var t' := t - {f[x]};
        var f' := map y | y in s' :: f[y];
        
        assert forall y | y in s' :: f'[y] in t';
        assert forall y1, y2 | y1 in s' && y2 in s' && y1 != y2 :: f'[y1] != f'[y2];
        
        InjectiveMappingCardinality(s', t', f');
        assert |s'| <= |t'|;
        assert |s| == |s'| + 1;
        assert |t| >= |t'| + 1;
        assert |s| <= |t|;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, scores: seq<int>) returns (result: int)
    requires ValidInput(n, scores)
    ensures ValidResult(scores, result)
// </vc-spec>
// <vc-code>
{
    var seen: set<int> := {};
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant n == |scores|
        invariant seen == set j | 0 <= j < i && scores[j] != 0 :: scores[j]
    {
        if scores[i] != 0 {
            seen := seen + {scores[i]};
        }
        i := i + 1;
    }
    
    assert i == n == |scores|;
    UniqueNonZeroScoresComplete(scores, seen);
    assert seen == UniqueNonZeroScores(scores);
    
    result := |seen|;
    
    // Prove result >= 1
    assert exists j :: 0 <= j < |scores| && scores[j] != 0;
    var idx :| 0 <= idx < |scores| && scores[idx] != 0;
    assert scores[idx] in UniqueNonZeroScores(scores);
    assert |UniqueNonZeroScores(scores)| >= 1;
    
    // Prove result <= |scores|
    UniqueNonZeroScoresBounded(scores);
    assert |seen| == |UniqueNonZeroScores(scores)|;
    assert |UniqueNonZeroScores(scores)| <= |scores|;
    assert result <= |scores|;
}
// </vc-code>


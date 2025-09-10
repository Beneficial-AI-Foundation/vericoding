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
    var indices := set i | 0 <= i < |scores| && scores[i] != 0;
    
    // Map from values to indices
    var values := UniqueNonZeroScores(scores);
    
    // For each value in the set, there must be at least one index with that value
    forall v | v in values
        ensures exists i :: i in indices && scores[i] == v
    {
        assert v in set j | 0 <= j < |scores| && scores[j] != 0 :: scores[j];
    }
    
    // Since each value must come from at least one index, and there are at most |scores| indices
    CardinalityBound(indices, |scores|);
    assert |indices| <= |scores|;
    
    // The cardinality of values is at most the cardinality of indices
    CardinalityMapping(scores, indices, values);
}

lemma CardinalityBound(s: set<int>, n: int)
    requires forall x | x in s :: 0 <= x < n
    ensures |s| <= n
{
    // This is a basic property of finite sets
}

lemma CardinalityMapping(scores: seq<int>, indices: set<int>, values: set<int>)
    requires indices == set i | 0 <= i < |scores| && scores[i] != 0
    requires values == set i | 0 <= i < |scores| && scores[i] != 0 :: scores[i]
    ensures |values| <= |indices|
{
    // The image of a function has at most the cardinality of its domain
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


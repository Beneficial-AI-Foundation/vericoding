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
        UniqueNonZeroScoresSubset(scores, i + 1, seen);
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
    assert |indices| <= |scores|;
    
    // The unique non-zero scores are at most as many as the indices where they appear
    assert UniqueNonZeroScores(scores) == set i | 0 <= i < |scores| && scores[i] != 0 :: scores[i];
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
    assert |seen| <= |scores|;
}
// </vc-code>


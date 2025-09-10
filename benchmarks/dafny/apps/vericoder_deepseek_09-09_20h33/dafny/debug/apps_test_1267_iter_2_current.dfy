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
lemma CountUniqueNonZero(scores: seq<int>)
    ensures |UniqueNonZeroScores(scores)| == |set i | 0 <= i < |scores| && scores[i] != 0 :: scores[i]|
{
}

lemma UniqueNonZeroSize(scores: seq<int>)
    ensures |UniqueNonZeroScores(scores)| >= 1
    decreases scores
{
    var i :| 0 <= i < |scores| && scores[i] != 0;
    assert scores[i] in UniqueNonZeroScores(scores);
    assert |UniqueNonZeroScores(scores)| >= 1;
}

lemma UniqueNonZeroBounded(scores: seq<int>)
    ensures |UniqueNonZeroScores(scores)| <= |scores|
    decreases scores
{
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
    var count := 0;
    
    var i := 0;
    while i < |scores|
        invariant 0 <= i <= |scores|
        invariant count == |set j | 0 <= j < i && scores[j] != 0 :: scores[j]|
        invariant seen == set j | 0 <= j < i && scores[j] != 0 :: scores[j]
    {
        if scores[i] != 0 && scores[i] !in seen {
            seen := seen + {scores[i]};
            count := count + 1;
        }
        i := i + 1;
    }
    
    result := count;
    
    CountUniqueNonZero(scores);
    UniqueNonZeroSize(scores);
    UniqueNonZeroBounded(scores);
    assert result == |UniqueNonZeroScores(scores)|;
}
// </vc-code>


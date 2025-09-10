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
lemma UniqueNonZeroScoresSize(scores: seq<int>)
    requires |scores| >= 1
    ensures |UniqueNonZeroScores(scores)| >= 0
    ensures |UniqueNonZeroScores(scores)| <= |scores|
{
}

lemma UniqueNonZeroScoresNonEmpty(scores: seq<int>)
    requires |scores| >= 1
    requires exists i :: 0 <= i < |scores| && scores[i] != 0
    ensures |UniqueNonZeroScores(scores)| >= 1
{
    var i :| 0 <= i < |scores| && scores[i] != 0;
    assert scores[i] in UniqueNonZeroScores(scores);
}

function SetFromSeq(scores: seq<int>): set<int>
{
    set i | 0 <= i < |scores| && scores[i] != 0 :: scores[i]
}

lemma SetFromSeqEqualsUniqueNonZero(scores: seq<int>)
    ensures SetFromSeq(scores) == UniqueNonZeroScores(scores)
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
    var uniqueScores: set<int> := {};
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant uniqueScores == set j | 0 <= j < i && scores[j] != 0 :: scores[j]
    {
        if scores[i] != 0 {
            uniqueScores := uniqueScores + {scores[i]};
        }
        i := i + 1;
    }
    
    result := |uniqueScores|;
    
    assert uniqueScores == UniqueNonZeroScores(scores);
    UniqueNonZeroScoresNonEmpty(scores);
    UniqueNonZeroScoresSize(scores);
}
// </vc-code>


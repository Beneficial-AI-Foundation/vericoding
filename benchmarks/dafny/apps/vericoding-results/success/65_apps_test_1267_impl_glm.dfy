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

// </vc-helpers>

// <vc-spec>
method solve(n: int, scores: seq<int>) returns (result: int)
    requires ValidInput(n, scores)
    ensures ValidResult(scores, result)
// </vc-spec>
// <vc-code>
{
    var uniqueSet: set<int> := {};
    for i := 0 to n
        invariant 0 <= i <= n
        invariant uniqueSet == set j | 0 <= j < i && scores[j] != 0 :: scores[j]
        invariant |uniqueSet| <= i
    {
        if scores[i] != 0 {
            uniqueSet := uniqueSet + {scores[i]};
        }
    }
    var nonZeroIndex :| 0 <= nonZeroIndex < n && scores[nonZeroIndex] != 0;
    assert scores[nonZeroIndex] in uniqueSet by {
        // This assertion follows directly from the loop invariant at i=n
        // and the fact that nonZeroIndex < n, so scores[nonZeroIndex] was processed
    }
    assert 1 <= |uniqueSet| by {
        // Since uniqueSet contains at least one element (scores[nonZeroIndex])
    }
    result := |uniqueSet|;
}
// </vc-code>


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
    var uniqueSet := {};
    for i := 0 to |scores|
        invariant uniqueSet == set j | 0 <= j < i && scores[j] != 0 :: scores[j]
    {
        if scores[i] != 0 {
            uniqueSet := uniqueSet + {scores[i]};
        }
    }
    result := |uniqueSet|;
}
// </vc-code>


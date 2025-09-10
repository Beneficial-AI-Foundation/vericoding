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
function UniqueNonZeroScoresSlice(scores: seq<int>, hi: int): set<int>
    requires 0 <= hi <= |scores|
{
    set j | 0 <= j < hi && scores[j] != 0 :: scores[j]
}
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
        invariant 0 <= i <= |scores|
        invariant uniqueSet == UniqueNonZeroScoresSlice(scores, i)
    {
        if scores[i] != 0 {
            uniqueSet := uniqueSet + {scores[i]};
        }
    }
    result := |uniqueSet|;
}
// </vc-code>


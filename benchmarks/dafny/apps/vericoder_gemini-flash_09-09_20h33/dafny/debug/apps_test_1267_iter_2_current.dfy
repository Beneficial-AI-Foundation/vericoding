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
function CountUniqueNonZero(scores: seq<int>): int
  reads scores
  ensures CountUniqueNonZero(scores) == |UniqueNonZeroScores(scores)|
{
  var seen := {};
  var count := 0;
  for i := 0 to |scores| - 1
    invariant 0 <= i <= |scores|
    invariant count == |UniqueNonZeroScores(scores[0..i])|
    invariant seen == UniqueNonZeroScores(scores[0..i])
  {
    if scores[i] != 0 && !(scores[i] in seen) {
      count := count + 1;
      seen := seen + {scores[i]};
    }
  }
  return count;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, scores: seq<int>) returns (result: int)
    requires ValidInput(n, scores)
    ensures ValidResult(scores, result)
// </vc-spec>
// <vc-code>
{
  result := CountUniqueNonZero(scores);
}
// </vc-code>


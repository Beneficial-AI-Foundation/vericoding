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
// No changes needed
// </vc-helpers>

// <vc-spec>
method solve(n: int, scores: seq<int>) returns (result: int)
    requires ValidInput(n, scores)
    ensures ValidResult(scores, result)
// </vc-spec>
// <vc-code>
{
  ghost var firstNonZero := -1;
  var count := 0;
  var seen: set<int> := {};
  for i := 0 to |scores|
    invariant 0 <= i <= |scores|
    invariant seen == set j | 0 <= j < i && scores[j] != 0 :: scores[j]
    invariant count == |seen|
    invariant count <= i
    invariant firstNonZero == -1 ==> !exists j :: 0 <= j < i && scores[j] != 0
    invariant firstNonZero != -1 ==> 0 <= firstNonZero < i && forall j :: 0 <= j < firstNonZero ==> scores[j] == 0 && scores[firstNonZero] != 0
    invariant firstNonZero != -1 ==> count >= 1
  {
    if firstNonZero == -1 && scores[i] != 0 {
      firstNonZero := i;
    }
    if 0 <= i < |scores| && scores[i] != 0 && scores[i] !in seen {
      seen := seen + {scores[i]};
      count := count + 1;
    }
  }
  result := count;
  assert result == |UniqueNonZeroScores(scores)| && result >= 1 && result <= |scores|;
}
// </vc-code>


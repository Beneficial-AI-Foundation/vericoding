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
  var s: set<int> := {};
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant s == set j | 0 <= j < i && scores[j] != 0 :: scores[j]
    invariant |s| <= i
    decreases n - i
  {
    if scores[i] != 0 {
      s := s + {scores[i]};
    }
    i := i + 1;
  }
  assert i == n;
  assert s == set j | 0 <= j < n && scores[j] != 0 :: scores[j];
  assert n == |scores|;
  assert s == UniqueNonZeroScores(scores);

  var k :| 0 <= k < |scores| && scores[k] != 0;
  assert scores[k] in UniqueNonZeroScores(scores);
  assert scores[k] in s;
  assert |s| >= 1;

  result := |s|;
}
// </vc-code>


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
  var count: int := 0;
  var i: int := 0;
  while i < n
    invariant 0 <= i <= n
    invariant s == set j | 0 <= j < i && scores[j] != 0 :: scores[j]
    invariant count == |s|
    invariant count <= i
    invariant (exists j :: 0 <= j < i && scores[j] != 0) ==> count >= 1
  {
    if scores[i] != 0 {
      if scores[i] !in s {
        s := s + {scores[i]};
        count := count + 1;
      }
    }
    i := i + 1;
  }
  assert n == |scores|;
  assert s == set j | 0 <= j < |scores| && scores[j] != 0 :: scores[j];
  result := count;
}
// </vc-code>


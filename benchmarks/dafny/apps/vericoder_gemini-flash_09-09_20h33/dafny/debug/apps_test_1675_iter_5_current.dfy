predicate ValidInput(n: int, teams: seq<(int, int)>)
{
  n >= 2 && |teams| == n &&
  (forall i :: 0 <= i < n ==> teams[i].0 != teams[i].1) &&
  (forall i :: 0 <= i < n ==> |set j | 0 <= j < n && teams[j].0 == teams[i].1| <= n - 1)
}

predicate ValidOutput(n: int, teams: seq<(int, int)>, result: seq<(int, int)>)
  requires |teams| == n
{
  |result| == n &&
  (forall i :: 0 <= i < n ==> result[i].0 + result[i].1 == 2 * (n - 1)) &&
  (forall i :: 0 <= i < n ==> result[i].0 >= n - 1) &&
  (forall i :: 0 <= i < n ==> result[i].1 >= 0) &&
  (forall i :: 0 <= i < n ==> 
    var homeCount := |set j | 0 <= j < n && teams[j].0 == teams[i].1|;
    result[i].0 == (n - 1) + homeCount &&
    result[i].1 == (n - 1) - homeCount)
}

// <vc-helpers>
function countOccurrences(teams: seq<(int, int)>, target: int): int
  reads teams
  ensures countOccurrences(teams, target) >= 0
  ensures countOccurrences(teams, target) <= |teams|
{
  var count := 0;
  var i := 0;
  while i < |teams|
    invariant 0 <= i <= |teams|
    invariant count == |set j | 0 <= j < i && teams[j].0 == target|
  {
    if teams[i].0 == target {
      count := count + 1;
    }
    i := i + 1;
  }
  return count;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, teams: seq<(int, int)>) returns (result: seq<(int, int)>)
  requires ValidInput(n, teams)
  ensures ValidOutput(n, teams, result)
// </vc-spec>
// <vc-code>
{
  var resultSeq: seq<(int, int)> := new seq<(int, int)>(n, (k) => (0, 0));
  for i := 0 to n - 1
    invariant 0 <= i <= n
    invariant |resultSeq| == n
    invariant forall k :: 0 <= k < i ==> 
      var homeCount := countOccurrences(teams, teams[k].1);
      resultSeq[k].0 == (n - 1) + homeCount &&
      resultSeq[k].1 == (n - 1) - homeCount
    invariant forall k :: i <= k < n ==> resultSeq[k] == (0, 0)
  {
    var homeCount := countOccurrences(teams, teams[i].1);
    var scoreHome := (n - 1) + homeCount;
    var scoreAway := (n - 1) - homeCount;
    
    resultSeq[i] := (scoreHome, scoreAway);
  }
  return resultSeq;
}
// </vc-code>


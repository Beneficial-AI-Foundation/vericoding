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
lemma CountSetCardinality(n: int, teams: seq<(int, int)>, i: int)
  requires n >= 2
  requires |teams| == n
  requires 0 <= i < n
  requires forall k :: 0 <= k < n ==> |set j | 0 <= j < n && teams[j].0 == teams[k].1| <= n - 1
  ensures var homeCount := |set j | 0 <= j < n && teams[j].0 == teams[i].1|;
          0 <= homeCount <= n - 1
{
  var homeCount := |set j | 0 <= j < n && teams[j].0 == teams[i].1|;
  // The precondition directly gives us that homeCount <= n - 1
  assert homeCount <= n - 1;
  // Non-negativity follows from set cardinality
  assert homeCount >= 0;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, teams: seq<(int, int)>) returns (result: seq<(int, int)>)
  requires ValidInput(n, teams)
  ensures ValidOutput(n, teams, result)
// </vc-spec>
// <vc-code>
{
  result := [];
  var idx := 0;
  
  while idx < n
    invariant 0 <= idx <= n
    invariant |result| == idx
    invariant forall k :: 0 <= k < idx ==> 
      var homeCount := |set j | 0 <= j < n && teams[j].0 == teams[k].1|;
      result[k].0 == (n - 1) + homeCount &&
      result[k].1 == (n - 1) - homeCount
    invariant forall k :: 0 <= k < idx ==> result[k].0 + result[k].1 == 2 * (n - 1)
    invariant forall k :: 0 <= k < idx ==> result[k].0 >= n - 1
    invariant forall k :: 0 <= k < idx ==> result[k].1 >= 0
  {
    var homeCount := |set j | 0 <= j < n && teams[j].0 == teams[idx].1|;
    CountSetCardinality(n, teams, idx);
    
    var homeGames := (n - 1) + homeCount;
    var awayGames := (n - 1) - homeCount;
    
    result := result + [(homeGames, awayGames)];
    idx := idx + 1;
  }
}
// </vc-code>


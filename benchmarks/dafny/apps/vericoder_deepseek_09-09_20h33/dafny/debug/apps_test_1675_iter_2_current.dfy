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
lemma CountLemma(n: int, teams: seq<(int, int)>, i: int)
  requires ValidInput(n, teams)
  requires 0 <= i < n
  ensures |set j | 0 <= j < n && teams[j].0 == teams[i].1| == |set j | 0 <= j < n && teams[j].0 == teams[i].1|
{
}

lemma HomeCountProperty(n: int, teams: seq<(int, int)>, i: int)
  requires ValidInput(n, teams)
  requires 0 <= i < n
  ensures var homeCount := |set j | 0 <= j < n && teams[j].0 == teams[i].1|;
           homeCount >= 0 && homeCount <= n - 1
{
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
  var i := 0;
  while i < n 
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> 
      var homeCount := |set j | 0 <= j < n && teams[j].0 == teams[k].1|;
      result[k] == ((n - 1) + homeCount, (n - 1) - homeCount)
  {
    var homeCount := |set j | 0 <= j < n && teams[j].0 == teams[i].1|;
    result := result + [((n - 1) + homeCount, (n - 1) - homeCount)];
    i := i + 1;
  }
}
// </vc-code>


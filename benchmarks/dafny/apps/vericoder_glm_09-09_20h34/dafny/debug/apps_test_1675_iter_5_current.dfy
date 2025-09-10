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
lemma HomeCountBounds(n: int, teams: seq<(int, int)>, i: int)
  requires ValidInput(n, teams)
  requires 0 <= i < n
  ensures var homeCount := |set j | 0 <= j < n && teams[j].0 == teams[i].1|;
          homeCount <= n - 1
{
  assert ValidInput(n, teams);
  assert forall i :: 0 <= i < n ==> |set j | 0 <= j < n && teams[j].0 == teams[i].1| <= n - 1;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, teams: seq<(int, int)>) returns (result: seq<(int, int)>)
  requires ValidInput(n, teams)
  ensures ValidOutput(n, teams, result)
// </vc-spec>
// <vc-code>
{
  var res := new (int, int)[n];
  for i := 0 to n
    invariant forall idx :: 0 <= idx < i ==> 
        var homeCount := |set j | 0 <= j < n && teams[j].0 == teams[idx].1|;
        res[idx] == ((n-1)+homeCount, (n-1)-homeCount)
  {
    var a := teams[i].1;
    var count := 0;
    for j := 0 to n
      invariant 0 <= j <= n
      invariant count == |set k | 0 <= k < j && teams[k].0 == a|
    {
      if j < n && teams[j].0 == a {
        count := count + 1;
      }
    }
    res[i] := ((n - 1) + count, (n - 1) - count);
  }
  return res[..];
}
// </vc-code>


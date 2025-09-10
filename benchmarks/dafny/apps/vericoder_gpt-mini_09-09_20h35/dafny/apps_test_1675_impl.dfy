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
function CountHome(teams: seq<(int, int)>, key: int): int
{
  |set j | 0 <= j < |teams| && teams[j].0 == key|
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, teams: seq<(int, int)>) returns (result: seq<(int, int)>)
  requires ValidInput(n, teams)
  ensures ValidOutput(n, teams, result)
// </vc-spec>
// <vc-code>
{
  var a := new (int, int)[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> a[k].0 + a[k].1 == 2 * (n - 1)
    invariant forall k :: 0 <= k < i ==> a[k].0 >= n - 1 && a[k].1 >= 0
    invariant forall k :: 0 <= k < i ==>
      a[k].0 == (n - 1) + CountHome(teams, teams[k].1) &&
      a[k].1 == (n - 1) - CountHome(teams, teams[k].1)
  {
    var hc := CountHome(teams, teams[i].1);
    a[i] := ((n - 1) + hc, (n - 1) - hc);
    i := i + 1;
  }
  result := a[..];
}
// </vc-code>


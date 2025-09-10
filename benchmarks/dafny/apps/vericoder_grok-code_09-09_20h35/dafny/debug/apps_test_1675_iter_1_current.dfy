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
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, teams: seq<(int, int)>) returns (result: seq<(int, int)>)
  requires ValidInput(n, teams)
  ensures ValidOutput(n, teams, result)
// </vc-spec>
// <vc-code>
var result: seq<(int, int)> := [];
  for i := 0 to n - 1 {
    var homeCount := 0;
    for j := 0 to n - 1 {
      if teams[j].0 == teams[i].1 {
        homeCount := homeCount + 1;
      }
    }
    var r0 := (n - 1) + homeCount;
    var r1 := (n - 1) - homeCount;
    result := result + [(r0, r1)];
  }
// </vc-code>


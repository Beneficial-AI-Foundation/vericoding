predicate ValidInput(cities: seq<int>)
{
  |cities| >= 2 &&
  forall i, j :: 0 <= i < j < |cities| ==> cities[i] < cities[j]
}

function MinDistance(cities: seq<int>, i: int): int
  requires ValidInput(cities)
  requires 0 <= i < |cities|
{
  if i == 0 then
    cities[1] - cities[0]
  else if i == |cities| - 1 then
    cities[i] - cities[i-1]
  else
    var left_dist := cities[i] - cities[i-1];
    var right_dist := cities[i+1] - cities[i];
    if left_dist <= right_dist then left_dist else right_dist
}

function MaxDistance(cities: seq<int>, i: int): int
  requires ValidInput(cities)
  requires 0 <= i < |cities|
{
  if i == 0 then
    cities[|cities|-1] - cities[0]
  else if i == |cities| - 1 then
    cities[i] - cities[0]
  else
    var dist_to_first := cities[i] - cities[0];
    var dist_to_last := cities[|cities|-1] - cities[i];
    if dist_to_first >= dist_to_last then dist_to_first else dist_to_last
}

predicate ValidOutput(cities: seq<int>, min_distances: seq<int>, max_distances: seq<int>)
{
  ValidInput(cities) &&
  |min_distances| == |cities| &&
  |max_distances| == |cities| &&
  forall i :: 0 <= i < |cities| ==> 
    min_distances[i] == MinDistance(cities, i) &&
    max_distances[i] == MaxDistance(cities, i) &&
    min_distances[i] > 0 &&
    max_distances[i] > 0
}

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
method CalculateDistances(cities: seq<int>) returns (min_distances: seq<int>, max_distances: seq<int>)
  requires ValidInput(cities)
  ensures ValidOutput(cities, min_distances, max_distances)
// </vc-spec>
// <vc-code>
{
  var n := |cities|;
  var md := new int[n];
  var xd := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> md[k] == MinDistance(cities, k) && xd[k] == MaxDistance(cities, k)
  {
    if i == 0 {
      md[0] := cities[1] - cities[0];
      xd[0] := cities[n-1] - cities[0];
    } else if i == n - 1 {
      md[i] := cities[i] - cities[i-1];
      xd[i] := cities[i] - cities[0];
    } else {
      var left_dist := cities[i] - cities[i-1];
      var right_dist := cities[i+1] - cities[i];
      if left_dist <= right_dist {
        md[i] := left_dist;
      } else {
        md[i] := right_dist;
      }

      var dist_to_first := cities[i] - cities[0];
      var dist_to_last := cities[n-1] - cities[i];
      if dist_to_first >= dist_to_last {
        xd[i] := dist_to_first;
      } else {
        xd[i] := dist_to_last;
      }
    }
    i := i + 1;
  }
  min_distances := md[..];
  max_distances := xd[..];
}
// </vc-code>


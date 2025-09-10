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
// The helper functions and predicates are already defined in the preamble.
// No duplicate definitions are needed here, as that causes errors.
// The preamble defines them globally and they are accessible everywhere.
// </vc-helpers>

// <vc-spec>
method CalculateDistances(cities: seq<int>) returns (min_distances: seq<int>, max_distances: seq<int>)
  requires ValidInput(cities)
  ensures ValidOutput(cities, min_distances, max_distances)
// </vc-spec>
// <vc-code>
{
  var min_dists_arr := new int[|cities|];
  var max_dists_arr := new int[|cities|];

  var i := 0;
  while i < |cities|
    invariant 0 <= i <= |cities|
    invariant min_dists_arr.Length == |cities| && max_dists_arr.Length == |cities|
    invariant forall k :: 0 <= k < i ==> min_dists_arr[k] == MinDistance(cities, k)
    invariant forall k :: 0 <= k < i ==> max_dists_arr[k] == MaxDistance(cities, k)
    invariant forall k :: i <= k < |cities| ==> min_dists_arr[k] == 0 // Default value for arrays
    invariant forall k :: i <= k < |cities| ==> max_dists_arr[k] == 0 // Default value for arrays
  {
    min_dists_arr[i] := MinDistance(cities, i);
    max_dists_arr[i] := MaxDistance(cities, i);
    i := i + 1;
  }

  min_distances := min_dists_arr[..];
  max_distances := max_dists_arr[..];
}
// </vc-code>


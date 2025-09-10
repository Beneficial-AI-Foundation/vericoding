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
lemma MinDistancePositive(cities: seq<int>, i: int)
  requires ValidInput(cities)
  requires 0 <= i < |cities|
  ensures MinDistance(cities, i) > 0
{
  if i == 0 {
    assert cities[0] < cities[1];
    assert MinDistance(cities, i) == cities[1] - cities[0];
  } else if i == |cities| - 1 {
    assert cities[i-1] < cities[i];
    assert MinDistance(cities, i) == cities[i] - cities[i-1];
  } else {
    assert cities[i-1] < cities[i];
    assert cities[i] < cities[i+1];
    var left_dist := cities[i] - cities[i-1];
    var right_dist := cities[i+1] - cities[i];
    assert left_dist > 0;
    assert right_dist > 0;
    if left_dist <= right_dist {
      assert MinDistance(cities, i) == left_dist;
    } else {
      assert MinDistance(cities, i) == right_dist;
    }
  }
}

lemma MaxDistancePositive(cities: seq<int>, i: int)
  requires ValidInput(cities)
  requires 0 <= i < |cities|
  ensures MaxDistance(cities, i) > 0
{
  if i == 0 || i == |cities| - 1 {
    assert cities[0] < cities[|cities| - 1];
    assert MaxDistance(cities, i) == cities[|cities| - 1] - cities[0];
  } else {
    var dist_to_first := cities[i] - cities[0];
    var dist_to_last := cities[|cities| - 1] - cities[i];
    assert dist_to_first > 0;
    assert dist_to_last > 0;
    if dist_to_first >= dist_to_last {
      assert MaxDistance(cities, i) == dist_to_first;
    } else {
      assert MaxDistance(cities, i) == dist_to_last;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method CalculateDistances(cities: seq<int>) returns (min_distances: seq<int>, max_distances: seq<int>)
  requires ValidInput(cities)
  ensures ValidOutput(cities, min_distances, max_distances)
// </vc-spec>
// <vc-code>
{
  var n := |cities|;
  min_distances := new int[n];
  max_distances := new int[n];
  for i := 0 to n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> 
      min_distances[j] == MinDistance(cities, j) &&
      max_distances[j] == MaxDistance(cities, j) &&
      min_distances[j] > 0 &&
      max_distances[j] > 0
  {
    MinDistancePositive(cities, i);
    MaxDistancePositive(cities, i);
    min_distances[i] := MinDistance(cities, i);
    max_distances[i] := MaxDistance(cities, i);
  }
}
// </vc-code>


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
    assert cities[1] > cities[0];
  } else if i == |cities| - 1 {
    assert cities[i] > cities[i-1];
  } else {
    assert cities[i] > cities[i-1];
    assert cities[i+1] > cities[i];
  }
}

lemma MaxDistancePositive(cities: seq<int>, i: int)
  requires ValidInput(cities)
  requires 0 <= i < |cities|
  ensures MaxDistance(cities, i) > 0
{
  if i == 0 {
    assert cities[|cities|-1] > cities[0];
  } else if i == |cities| - 1 {
    assert cities[i] > cities[0];
  } else {
    assert cities[i] > cities[0];
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
  min_distances := [];
  max_distances := [];
  
  var i := 0;
  while i < |cities|
    invariant 0 <= i <= |cities|
    invariant |min_distances| == i
    invariant |max_distances| == i
    invariant forall j :: 0 <= j < i ==> 
      min_distances[j] == MinDistance(cities, j) &&
      max_distances[j] == MaxDistance(cities, j)
    invariant forall j :: 0 <= j < i ==> 
      min_distances[j] > 0 && max_distances[j] > 0
  {
    var min_dist: int;
    var max_dist: int;
    
    if i == 0 {
      min_dist := cities[1] - cities[0];
      max_dist := cities[|cities|-1] - cities[0];
    } else if i == |cities| - 1 {
      min_dist := cities[i] - cities[i-1];
      max_dist := cities[i] - cities[0];
    } else {
      var left_dist := cities[i] - cities[i-1];
      var right_dist := cities[i+1] - cities[i];
      min_dist := if left_dist <= right_dist then left_dist else right_dist;
      
      var dist_to_first := cities[i] - cities[0];
      var dist_to_last := cities[|cities|-1] - cities[i];
      max_dist := if dist_to_first >= dist_to_last then dist_to_first else dist_to_last;
    }
    
    MinDistancePositive(cities, i);
    MaxDistancePositive(cities, i);
    
    min_distances := min_distances + [min_dist];
    max_distances := max_distances + [max_dist];
    
    i := i + 1;
  }
}
// </vc-code>


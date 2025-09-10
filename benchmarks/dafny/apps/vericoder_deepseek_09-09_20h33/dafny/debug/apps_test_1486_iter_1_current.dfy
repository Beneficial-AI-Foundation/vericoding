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
lemma MinDistanceLemma(cities: seq<int>, i: int, left_dist: int, right_dist: int, dist_to_first: int, dist_to_last: int)
  requires ValidInput(cities)
  requires 0 <= i < |cities|
  requires if i == 0 then true else cities[i] - cities[i-1] == left_dist
  requires if i == |cities| - 1 then true else cities[i+1] - cities[i] == right_dist
  requires cities[i] - cities[0] == dist_to_first
  requires cities[|cities|-1] - cities[i] == dist_to_last
  ensures min_distances[i] == MinDistance(cities, i)
  ensures max_distances[i] == MaxDistance(cities, i)
{
}

lemma SequenceProperties(cities: seq<int>)
  requires ValidInput(cities)
  ensures forall i :: 0 <= i < |cities| ==> MinDistance(cities, i) > 0 && MaxDistance(cities, i) > 0
{
}
// </vc-helpers>

// <vc-spec>
method CalculateDistances(cities: seq<int>) returns (min_distances: seq<int>, max_distances: seq<int>)
  requires ValidInput(cities)
  ensures ValidOutput(cities, min_distances, max_distances)
// </vc-spec>
// <vc-code>
{
  min_distances := new int[|cities|];
  max_distances := new int[|cities|];
  
  var n := |cities|;
  
  for i := 0 to n - 1
    invariant 0 <= i <= n
    invariant |min_distances| == n
    invariant |max_distances| == n
    invariant forall j :: 0 <= j < i ==> min_distances[j] == MinDistance(cities, j)
    invariant forall j :: 0 <= j < i ==> max_distances[j] == MaxDistance(cities, j)
    invariant forall j :: 0 <= j < i ==> min_distances[j] > 0 && max_distances[j] > 0
  {
    if i == 0 {
      min_distances[i] := cities[1] - cities[0];
      max_distances[i] := cities[n-1] - cities[0];
    } else if i == n - 1 {
      min_distances[i] := cities[i] - cities[i-1];
      max_distances[i] := cities[i] - cities[0];
    } else {
      var left_dist := cities[i] - cities[i-1];
      var right_dist := cities[i+1] - cities[i];
      var dist_to_first := cities[i] - cities[0];
      var dist_to_last := cities[n-1] - cities[i];
      
      if left_dist <= right_dist {
        min_distances[i] := left_dist;
      } else {
        min_distances[i] := right_dist;
      }
      
      if dist_to_first >= dist_to_last {
        max_distances[i] := dist_to_first;
      } else {
        max_distances[i] := dist_to_last;
      }
    }
    
    MinDistanceLemma(cities, i, cities[i] - cities[i-1], cities[i+1] - cities[i], cities[i] - cities[0], cities[n-1] - cities[i]);
  }
  
  SequenceProperties(cities);
}
// </vc-code>


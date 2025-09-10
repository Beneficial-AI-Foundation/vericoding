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
lemma MinDistanceLemma(cities: seq<int>, i: int)
  requires ValidInput(cities)
  requires 0 <= i < |cities|
  ensures if i == 0 then 
            MinDistance(cities, i) == cities[1] - cities[0]
          else if i == |cities| - 1 then
            MinDistance(cities, i) == cities[i] - cities[i-1]
          else
            MinDistance(cities, i) == (if cities[i] - cities[i-1] <= cities[i+1] - cities[i] then cities[i] - cities[i-1] else cities[i+1] - cities[i])
{
  // Body is omitted since the lemma is essentially just unfolding the function definition
}

lemma MaxDistanceLemma(cities: seq<int>, i: int)
  requires ValidInput(cities)
  requires 0 <= i < |cities|
  ensures if i == 0 then 
            MaxDistance(cities, i) == cities[|cities|-1] - cities[0]
          else if i == |cities| - 1 then
            MaxDistance(cities, i) == cities[i] - cities[0]
          else
            MaxDistance(cities, i) == (if cities[i] - cities[0] >= cities[|cities|-1] - cities[i] then cities[i] - cities[0] else cities[|cities|-1] - cities[i])
{
  // Body is omitted since the lemma is essentially just unfolding the function definition
}

lemma SequenceProperties(cities: seq<int>)
  requires ValidInput(cities)
  ensures forall i :: 0 <= i < |cities| ==> MinDistance(cities, i) > 0 && MaxDistance(cities, i) > 0
{
  forall i | 0 <= i < |cities|
    ensures MinDistance(cities, i) > 0 && MaxDistance(cities, i) > 0
  {
    MinDistanceLemma(cities, i);
    MaxDistanceLemma(cities, i);
    
    if i == 0 {
      assert cities[1] > cities[0] by { assert ValidInput(cities); }
      assert cities[|cities|-1] > cities[0] by { assert ValidInput(cities); }
    } else if i == |cities| - 1 {
      assert cities[i] > cities[i-1] by { assert ValidInput(cities); }
      assert cities[i] > cities[0] by { assert ValidInput(cities); }
    } else {
      assert cities[i] > cities[i-1] by { assert ValidInput(cities); }
      assert cities[i+1] > cities[i] by { assert ValidInput(cities); }
      assert cities[i] > cities[0] by { assert ValidInput(cities); }
      assert cities[|cities|-1] > cities[i] by { assert ValidInput(cities); }
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
  var min_arr := new int[n];
  var max_arr := new int[n];
  
  for i := 0 to n - 1
    invariant 0 <= i <= n
    invariant min_arr.Length == n
    invariant max_arr.Length == n
    invariant forall j :: 0 <= j < i ==> min_arr[j] == MinDistance(cities, j)
    invariant forall j :: 0 <= j < i ==> max_arr[j] == MaxDistance(cities, j)
    invariant forall j :: 0 <= j < i ==> min_arr[j] > 0 && max_arr[j] > 0
  {
    MinDistanceLemma(cities, i);
    MaxDistanceLemma(cities, i);
    
    if i == 0 {
      min_arr[i] := cities[1] - cities[0];
      max_arr[i] := cities[n-1] - cities[0];
    } else if i == n - 1 {
      min_arr[i] := cities[i] - cities[i-1];
      max_arr[i] := cities[i] - cities[0];
    } else {
      var left_dist := cities[i] - cities[i-1];
      var right_dist := cities[i+1] - cities[i];
      var dist_to_first := cities[i] - cities[0];
      var dist_to_last := cities[n-1] - cities[i];
      
      if left_dist <= right_dist {
        min_arr[i] := left_dist;
      } else {
        min_arr[i] := right_dist;
      }
      
      if dist_to_first >= dist_to_last {
        max_arr[i] := dist_to_first;
      } else {
        max_arr[i] := dist_to_last;
      }
    }
    
    assert min_arr[i] == MinDistance(cities, i);
    assert max_arr[i] == MaxDistance(cities, i);
    assert min_arr[i] > 0;
    assert max_arr[i] > 0;
  }
  
  min_distances := min_arr[..];
  max_distances := max_arr[..];
  SequenceProperties(cities);
}
// </vc-code>


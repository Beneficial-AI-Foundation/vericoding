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
lemma DiffPositiveFromStrictlyIncreasing(cities: seq<int>, i: int, j: int)
  requires ValidInput(cities)
  requires 0 <= i < j < |cities|
  ensures cities[j] - cities[i] > 0
{
  assert cities[i] < cities[j];
}

lemma MinDistancePositive(cities: seq<int>, i: int)
  requires ValidInput(cities)
  requires 0 <= i < |cities|
  ensures MinDistance(cities, i) > 0
{
  if i == 0 {
    assert |cities| >= 2;
    assert MinDistance(cities, i) == cities[1] - cities[0];
    DiffPositiveFromStrictlyIncreasing(cities, 0, 1);
  } else if i == |cities| - 1 {
    assert i > 0;
    assert MinDistance(cities, i) == cities[i] - cities[i-1];
    DiffPositiveFromStrictlyIncreasing(cities, i - 1, i);
  } else {
    var left := cities[i] - cities[i-1];
    var right := cities[i+1] - cities[i];
    assert 0 < i;
    assert i + 1 < |cities|;
    DiffPositiveFromStrictlyIncreasing(cities, i - 1, i);
    DiffPositiveFromStrictlyIncreasing(cities, i, i + 1);
    if left <= right {
      assert MinDistance(cities, i) == left;
    } else {
      assert MinDistance(cities, i) == right;
    }
  }
}

lemma MaxDistancePositive(cities: seq<int>, i: int)
  requires ValidInput(cities)
  requires 0 <= i < |cities|
  ensures MaxDistance(cities, i) > 0
{
  if i == 0 {
    assert |cities| >= 2;
    assert MaxDistance(cities, i) == cities[|cities| - 1] - cities[0];
    DiffPositiveFromStrictlyIncreasing(cities, 0, |cities| - 1);
  } else if i == |cities| - 1 {
    assert i > 0;
    assert MaxDistance(cities, i) == cities[i] - cities[0];
    DiffPositiveFromStrictlyIncreasing(cities, 0, i);
  } else {
    var dist_to_first := cities[i] - cities[0];
    var dist_to_last := cities[|cities| - 1] - cities[i];
    assert 0 < i;
    assert i < |cities| - 1;
    DiffPositiveFromStrictlyIncreasing(cities, 0, i);
    DiffPositiveFromStrictlyIncreasing(cities, i, |cities| - 1);
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
  min_distances := seq(i: int | 0 <= i < |cities|, MinDistance(cities, i));
  max_distances := seq(i: int | 0 <= i < |cities|, MaxDistance(cities, i));

  assert |min_distances| == |cities|;
  assert |max_distances| == |cities|;

  forall i:int | 0 <= i < |cities|
    ensures min_distances[i] == MinDistance(cities, i) &&
            max_distances[i] == MaxDistance(cities, i) &&
            min_distances[i] > 0 &&
            max_distances[i] > 0
  {
    assert min_distances[i] == MinDistance(cities, i);
    assert max_distances[i] == MaxDistance(cities, i);
    MinDistancePositive(cities, i);
    MaxDistancePositive(cities, i);
    assert min_distances[i] > 0;
    assert max_distances[i] > 0;
  }
}
// </vc-code>


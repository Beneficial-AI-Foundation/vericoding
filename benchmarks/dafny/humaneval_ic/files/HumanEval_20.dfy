Given a list of numbers with at least two elements, find the pair of numbers with the smallest absolute difference between them. Return the pair as a tuple ordered from smaller to larger value. The implementation uses nested loops to compare all pairs and track the minimum difference found.

// ======= TASK =======
// Given a list of numbers with at least two elements, find the pair of numbers 
// with the smallest absolute difference between them. Return the pair as a tuple 
// ordered from smaller to larger value.

// ======= SPEC REQUIREMENTS =======
function AbsDiff(x: real, y: real): real
{
  if x >= y then x - y else y - x
}

predicate ValidInput(numbers: seq<real>)
{
  |numbers| >= 2
}

predicate IsOptimalPair(numbers: seq<real>, pair: (real, real))
{
  pair.0 in numbers &&
  pair.1 in numbers &&
  pair.0 <= pair.1 &&
  forall i, j :: 0 <= i < |numbers| && 0 <= j < |numbers| && i != j ==>
    AbsDiff(numbers[i], numbers[j]) >= AbsDiff(pair.0, pair.1)
}

// ======= HELPERS =======

// ======= MAIN METHOD =======
method find_closest_elements(numbers: seq<real>) returns (result: (real, real))
  requires ValidInput(numbers)
  ensures IsOptimalPair(numbers, result)
{
  var min_diff := AbsDiff(numbers[0], numbers[1]);
  var closest_pair := (numbers[0], numbers[1]);

  for i := 0 to |numbers| - 1
    invariant closest_pair.0 in numbers
    invariant closest_pair.1 in numbers
    invariant min_diff == AbsDiff(closest_pair.0, closest_pair.1)
    invariant forall k, l :: 0 <= k < |numbers| && 0 <= l < |numbers| && k != l && k < i ==>
      AbsDiff(numbers[k], numbers[l]) >= min_diff
  {
    for j := i + 1 to |numbers|
      invariant closest_pair.0 in numbers
      invariant closest_pair.1 in numbers
      invariant min_diff == AbsDiff(closest_pair.0, closest_pair.1)
      invariant forall k, l :: 0 <= k < |numbers| && 0 <= l < |numbers| && k != l && 
                ((k < i) || (k == i && i < l < j)) ==>
        AbsDiff(numbers[k], numbers[l]) >= min_diff
    {
      var diff := AbsDiff(numbers[i], numbers[j]);
      if diff < min_diff {
        min_diff := diff;
        closest_pair := (numbers[i], numbers[j]);
      }
    }
  }

  if closest_pair.0 <= closest_pair.1 {
    result := closest_pair;
  } else {
    result := (closest_pair.1, closest_pair.0);
  }
}

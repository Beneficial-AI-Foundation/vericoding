// <vc-preamble>

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
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method find_closest_elements(numbers: seq<real>) returns (result: (real, real))
  requires ValidInput(numbers)
  ensures IsOptimalPair(numbers, result)
// </vc-spec>
// <vc-code>
{
  var p0 := numbers[0];
  var p1 := numbers[1];
  if p0 > p1 {
    p0, p1 := p1, p0;
  }
  result := (p0, p1);
  var min_diff: real := result.1 - result.0;

  var i: int := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant result.0 in numbers && result.1 in numbers
    invariant result.0 <= result.1
    invariant min_diff == AbsDiff(result.0, result.1)
    invariant forall a, b :: 0 <= a < b < |numbers| && a < i ==> AbsDiff(numbers[a], numbers[b]) >= min_diff
  {
    var j: int := i + 1;
    while j < |numbers|
      invariant 0 <= i < |numbers|
      invariant i + 1 <= j <= |numbers|
      invariant result.0 in numbers && result.1 in numbers
      invariant result.0 <= result.1
      invariant min_diff == AbsDiff(result.0, result.1)
      invariant forall a, b :: 0 <= a < b < |numbers| && (a < i || (a == i && b < j)) ==> AbsDiff(numbers[a], numbers[b]) >= min_diff
    {
      var current_diff := AbsDiff(numbers[i], numbers[j]);
      if current_diff < min_diff {
        min_diff := current_diff;
        if numbers[i] <= numbers[j] {
          result := (numbers[i], numbers[j]);
        } else {
          result := (numbers[j], numbers[i]);
        }
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

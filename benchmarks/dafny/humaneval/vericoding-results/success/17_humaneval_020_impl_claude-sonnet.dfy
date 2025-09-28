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
/* helper modified by LLM (iteration 3): added lemma to help with verification */
lemma DiffCommutative(x: real, y: real)
  ensures AbsDiff(x, y) == AbsDiff(y, x)
{
}

lemma PairInNumbers(numbers: seq<real>, i: int, j: int)
  requires 0 <= i < |numbers| && 0 <= j < |numbers|
  ensures numbers[i] in numbers && numbers[j] in numbers
{
}
// </vc-helpers>

// <vc-spec>
method find_closest_elements(numbers: seq<real>) returns (result: (real, real))
  requires ValidInput(numbers)
  ensures IsOptimalPair(numbers, result)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): fixed invariants and verification issues */
  var minDiff := AbsDiff(numbers[0], numbers[1]);
  var bestPair := if numbers[0] <= numbers[1] then (numbers[0], numbers[1]) else (numbers[1], numbers[0]);
  
  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant bestPair.0 in numbers && bestPair.1 in numbers
    invariant bestPair.0 <= bestPair.1
    invariant AbsDiff(bestPair.0, bestPair.1) == minDiff
    invariant forall k, l :: 0 <= k < i && 0 <= l < |numbers| && k != l ==> AbsDiff(numbers[k], numbers[l]) >= minDiff
  {
    var j := 0;
    while j < |numbers|
      invariant 0 <= j <= |numbers|
      invariant bestPair.0 in numbers && bestPair.1 in numbers
      invariant bestPair.0 <= bestPair.1
      invariant AbsDiff(bestPair.0, bestPair.1) == minDiff
      invariant forall k, l :: 0 <= k < i && 0 <= l < |numbers| && k != l ==> AbsDiff(numbers[k], numbers[l]) >= minDiff
      invariant forall l :: 0 <= l < j && i != l ==> AbsDiff(numbers[i], numbers[l]) >= minDiff
    {
      if i != j {
        var diff := AbsDiff(numbers[i], numbers[j]);
        if diff < minDiff {
          minDiff := diff;
          bestPair := if numbers[i] <= numbers[j] then (numbers[i], numbers[j]) else (numbers[j], numbers[i]);
        }
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
  result := bestPair;
}
// </vc-code>

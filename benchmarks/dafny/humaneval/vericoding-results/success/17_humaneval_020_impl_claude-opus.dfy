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
/* helper modified by LLM (iteration 2): Fixed indentation warning in exists clause */
function MinDiffPair(numbers: seq<real>, i: int, j: int): real
  requires 0 <= i < |numbers|
  requires 0 <= j < |numbers|
  requires i != j
{
  AbsDiff(numbers[i], numbers[j])
}

lemma MinDiffExists(numbers: seq<real>)
  requires ValidInput(numbers)
  ensures exists i, j :: 
    0 <= i < |numbers| && 0 <= j < |numbers| && i != j &&
    (forall k, l :: 0 <= k < |numbers| && 0 <= l < |numbers| && k != l ==> 
      MinDiffPair(numbers, i, j) <= MinDiffPair(numbers, k, l))
{
  var minDiff := MinDiffPair(numbers, 0, 1);
  var minI := 0;
  var minJ := 1;
  
  for i := 0 to |numbers|
    invariant 0 <= minI < |numbers| && 0 <= minJ < |numbers| && minI != minJ
    invariant minDiff == MinDiffPair(numbers, minI, minJ)
    invariant forall k, l :: 0 <= k < i && 0 <= l < |numbers| && k != l ==> 
      minDiff <= MinDiffPair(numbers, k, l)
  {
    for j := 0 to |numbers|
      invariant 0 <= minI < |numbers| && 0 <= minJ < |numbers| && minI != minJ
      invariant minDiff == MinDiffPair(numbers, minI, minJ)
      invariant forall k :: 0 <= k < j && k != i ==> 
        minDiff <= MinDiffPair(numbers, i, k)
      invariant forall k, l :: 0 <= k < i && 0 <= l < |numbers| && k != l ==> 
        minDiff <= MinDiffPair(numbers, k, l)
    {
      if i != j && MinDiffPair(numbers, i, j) < minDiff {
        minDiff := MinDiffPair(numbers, i, j);
        minI := i;
        minJ := j;
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
method find_closest_elements(numbers: seq<real>) returns (result: (real, real))
  requires ValidInput(numbers)
  ensures IsOptimalPair(numbers, result)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Implementation remains the same */
  var minDiff := AbsDiff(numbers[0], numbers[1]);
  var minI := 0;
  var minJ := 1;
  
  for i := 0 to |numbers|
    invariant 0 <= minI < |numbers| && 0 <= minJ < |numbers| && minI != minJ
    invariant minDiff == AbsDiff(numbers[minI], numbers[minJ])
    invariant forall k, l :: 0 <= k < i && 0 <= l < |numbers| && k != l ==> 
      AbsDiff(numbers[k], numbers[l]) >= minDiff
  {
    for j := i + 1 to |numbers|
      invariant 0 <= minI < |numbers| && 0 <= minJ < |numbers| && minI != minJ
      invariant minDiff == AbsDiff(numbers[minI], numbers[minJ])
      invariant forall k :: i + 1 <= k < j ==> 
        AbsDiff(numbers[i], numbers[k]) >= minDiff
      invariant forall k, l :: 0 <= k < i && 0 <= l < |numbers| && k != l ==> 
        AbsDiff(numbers[k], numbers[l]) >= minDiff
    {
      if AbsDiff(numbers[i], numbers[j]) < minDiff {
        minDiff := AbsDiff(numbers[i], numbers[j]);
        minI := i;
        minJ := j;
      }
    }
  }
  
  if numbers[minI] <= numbers[minJ] {
    result := (numbers[minI], numbers[minJ]);
  } else {
    result := (numbers[minJ], numbers[minI]);
  }
}
// </vc-code>

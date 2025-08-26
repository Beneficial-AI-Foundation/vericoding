/*
HumanEvalX 9
From a given list of integers, generate a list of rolling maximum element found until given moment in the sequence.
*/

// <vc-spec>
function isMax(m: int, numbers: seq<int>): bool
{
    m in numbers &&
    forall i :: 0 <= i < |numbers| ==> numbers[i] <= m

}

// <vc-helpers>
// </vc-helpers>

method max(numbers: seq<int>) returns (result: int)
requires numbers != []
ensures isMax(result, numbers)
// </vc-spec>
// <vc-code>
{
  result := numbers[0];
  var i := 1;
  
  while i < |numbers|
    invariant 1 <= i <= |numbers|
    invariant result in numbers
    invariant forall j :: 0 <= j < i ==> numbers[j] <= result
  {
    if numbers[i] > result {
      result := numbers[i];
    }
    i := i + 1;
  }
}
// </vc-code>
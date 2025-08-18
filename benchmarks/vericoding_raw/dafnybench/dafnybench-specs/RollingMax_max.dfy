/*
HumanEvalX 9
From a given list of integers, generate a list of rolling maximum element found until given moment in the sequence.
*/

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
// <vc-code>
{
  assume false;
}
// </vc-code>
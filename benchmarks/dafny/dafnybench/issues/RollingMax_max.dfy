// <vc-preamble>
/*
HumanEvalX 9
From a given list of integers, generate a list of rolling maximum element found until given moment in the sequence.
*/

function isMax(m: int, numbers: seq<int>): bool
{
    m in numbers &&
    forall i :: 0 <= i < |numbers| ==> numbers[i] <= m

}
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method max(numbers: seq<int>) returns (result: int)
requires numbers != []
ensures isMax(result, numbers)
// </vc-spec>
// <vc-code>
{
    result := numbers[0];
    for i := 1 to |numbers|
    invariant isMax(result, numbers[0..i])
    {
        if numbers[i] > result {
            result := numbers[i];
        }
    }
}
// </vc-code>

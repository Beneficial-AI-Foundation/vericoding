// <vc-preamble>

predicate ValidInput(numbers: seq<int>, delimiter: int)
{
    true // Any sequence and delimiter are valid inputs
}

predicate ValidOutput(numbers: seq<int>, delimiter: int, result: seq<int>)
{
    if |numbers| <= 1 then
        result == numbers
    else
        |result| == 2 * |numbers| - 1 &&
        (forall i :: 0 <= i < |numbers| ==> result[2 * i] == numbers[i]) &&
        (forall i :: 0 <= i < |numbers| - 1 ==> result[2 * i + 1] == delimiter)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method InsertDelimiter(numbers: seq<int>, delimiter: int) returns (result: seq<int>)
    requires ValidInput(numbers, delimiter)
    ensures ValidOutput(numbers, delimiter, result)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): Implemented using a while loop that builds the result by appending [delimiter, numbers[idx]] to the result in each iteration, with invariants matching the postcondition requirements. */
  if |numbers| <= 1 {
    result := numbers;
  } else {
    result := [numbers[0]];
    var idx := 1;
    while idx < |numbers|
      invariant 0 <= idx <= |numbers|
      invariant |result| == 2 * idx - 1
      invariant forall i :: 0 <= i < idx ==> result[2 * i] == numbers[i]
      invariant forall i :: 0 <= i < idx - 1 ==> result[2 * i + 1] == delimiter
    {
      result := result + [delimiter] + [numbers[idx]];
      idx := idx + 1;
    }
  }
}
// </vc-code>

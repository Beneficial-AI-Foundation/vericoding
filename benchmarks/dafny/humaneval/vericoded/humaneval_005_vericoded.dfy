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
  /* code modified by LLM (iteration 2): Fixed loop invariants and bounds */
  if |numbers| <= 1 {
    result := numbers;
  } else {
    result := [];
    var i := 0;
    while i < |numbers| - 1
      invariant 0 <= i <= |numbers| - 1
      invariant |result| == 2 * i
      invariant forall j :: 0 <= j < i ==> result[2 * j] == numbers[j]
      invariant forall j :: 0 <= j < i ==> result[2 * j + 1] == delimiter
    {
      result := result + [numbers[i], delimiter];
      i := i + 1;
    }
    result := result + [numbers[i]];
  }
}
// </vc-code>

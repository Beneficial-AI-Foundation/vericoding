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
function InsertDelimiterRecursive(numbers: seq<int>, delimiter: int): (result: seq<int>)
    requires |numbers| > 0
    ensures ValidOutput(numbers, delimiter, result)
    decreases |numbers|
{
    if |numbers| == 1 then
        numbers
    else
        var prefix := InsertDelimiterRecursive(numbers[..|numbers|-1], delimiter);
        prefix + [delimiter, numbers[|numbers|-1]]
}
// </vc-helpers>

// <vc-spec>
method InsertDelimiter(numbers: seq<int>, delimiter: int) returns (result: seq<int>)
    requires ValidInput(numbers, delimiter)
    ensures ValidOutput(numbers, delimiter, result)
// </vc-spec>
// <vc-code>
{
  if |numbers| <= 1 {
    result := numbers;
  } else {
    result := InsertDelimiterRecursive(numbers, delimiter);
  }
}
// </vc-code>

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
  if |numbers| <= 1 {
    result := numbers;
  } else {
    var r: seq<int> := [numbers[0]];
    var i := 1;
    while i < |numbers|
      invariant 1 <= i <= |numbers|
      invariant |r| == 2 * i - 1
      invariant (forall k :: 0 <= k < i ==> r[2 * k] == numbers[k])
      invariant (forall k :: 0 <= k < i - 1 ==> r[2 * k + 1] == delimiter)
      decreases |numbers| - i
    {
      r := r + [delimiter] + [numbers[i]];
      i := i + 1;
    }
    result := r;
  }
}
// </vc-code>

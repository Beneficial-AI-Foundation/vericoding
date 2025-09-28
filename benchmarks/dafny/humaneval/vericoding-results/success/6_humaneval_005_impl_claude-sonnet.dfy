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
/* helper modified by LLM (iteration 3): Added helper lemma to prove invariant maintenance */
lemma ArrayLengthHelper(i: int)
  requires i >= 0
  ensures 2 * (i + 1) - 1 == 2 * i + 1
{
  // trivial arithmetic lemma
}
// </vc-helpers>

// <vc-spec>
method InsertDelimiter(numbers: seq<int>, delimiter: int) returns (result: seq<int>)
    requires ValidInput(numbers, delimiter)
    ensures ValidOutput(numbers, delimiter, result)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Fixed invariant maintenance by restructuring loop to add delimiter first */
  if |numbers| <= 1 {
    result := numbers;
  } else {
    result := [numbers[0]];
    var i := 1;
    while i < |numbers|
      invariant 1 <= i <= |numbers|
      invariant |result| == 2 * i - 1
      invariant forall j :: 0 <= j < i ==> result[2 * j] == numbers[j]
      invariant forall j :: 0 <= j < i - 1 ==> result[2 * j + 1] == delimiter
    {
      result := result + [delimiter] + [numbers[i]];
      i := i + 1;
    }
  }
}
// </vc-code>

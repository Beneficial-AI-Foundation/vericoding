// <vc-preamble>
// ======= TASK =======
// Given a list of integers and a delimiter integer, insert the delimiter between every two consecutive elements in the list.

// ======= SPEC REQUIREMENTS =======
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
// ======= HELPERS =======
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method InsertDelimiter(numbers: seq<int>, delimiter: int) returns (result: seq<int>)
    requires ValidInput(numbers, delimiter)
    ensures ValidOutput(numbers, delimiter, result)
// </vc-spec>
// <vc-code>
{
    if |numbers| <= 1 {
        return numbers;
    }
    
    result := [];
    for i := 0 to |numbers|
        invariant 0 <= i <= |numbers|
        invariant if i == 0 then |result| == 0
                 else if i == 1 then |result| == 1 && result == [numbers[0]]
                 else |result| == 2 * i - 1
        invariant forall j :: 0 <= j < i ==> j < |numbers| && result[2 * j] == numbers[j]
        invariant forall j :: 0 <= j < i - 1 ==> result[2 * j + 1] == delimiter
    {
        if i == 0 {
            result := result + [numbers[i]];
        } else {
            result := result + [delimiter, numbers[i]];
        }
    }
}
// </vc-code>

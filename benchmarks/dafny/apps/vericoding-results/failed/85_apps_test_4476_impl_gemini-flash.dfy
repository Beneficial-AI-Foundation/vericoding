predicate ValidInput(input: seq<(int, int)>)
{
    forall i :: 0 <= i < |input| ==> input[i].0 >= 1 && input[i].1 >= 1
}

function MinMoves(a: int, b: int): int
    requires a >= 1 && b >= 1
{
    if a == b then 0
    else if a < b then
        if (b - a) % 2 == 1 then 1 else 2
    else
        if (a - b) % 2 == 0 then 1 else 2
}

predicate ValidOutput(input: seq<(int, int)>, result: seq<int>)
    requires ValidInput(input)
{
    |result| == |input| &&
    forall i :: 0 <= i < |input| ==> result[i] == MinMoves(input[i].0, input[i].1) &&
    forall i :: 0 <= i < |result| ==> result[i] >= 0
}

// <vc-helpers>
predicate ValidInput_Helper(input: seq<(int, int)>)
{
    forall i :: 0 <= i < |input| ==> input[i].0 >= 1 && input[i].1 >= 1
}

function MinMoves_Helper(a: int, b: int): int
    requires a >= 1 && b >= 1
{
    if a == b then 0
    else if a < b then
        if (b - a) % 2 == 1 then 1 else 2
    else
        if (a - b) % 2 == 0 then 1 else 2
}

predicate ValidOutput_Helper(input: seq<(int, int)>, result: seq<int>)
    requires ValidInput_Helper(input)
{
    |result| == |input| &&
    (forall i :: 0 <= i < |input| ==> result[i] == MinMoves_Helper(input[i].0, input[i].1)) &&
    (forall i :: 0 <= i < |result| ==> result[i] >= 0)
}
// </vc-helpers>

// <vc-spec>
method solve(input: seq<(int, int)>) returns (result: seq<int>)
    requires ValidInput(input)
    ensures ValidOutput(input, result)
// </vc-spec>
// <vc-code>
{
    var result_array := new int[|input|];
    if |input| == 0 {
        return [];
    }
    for i := 0 to |input| - 1
        invariant 0 <= i <= |input|
        invariant forall j :: 0 <= j < i ==> result_array[j] == MinMoves(input[j].0, input[j].1)
        invariant forall j :: 0 <= j < i ==> result_array[j] >= 0
        invariant result_array.Length == |input|
    {
        result_array[i] := MinMoves(input[i].0, input[i].1);
    }
    return result_array[..];
}
// </vc-code>


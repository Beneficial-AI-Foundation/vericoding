// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(input: seq<(int, int)>) returns (result: seq<int>)
    requires ValidInput(input)
    ensures ValidOutput(input, result)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>

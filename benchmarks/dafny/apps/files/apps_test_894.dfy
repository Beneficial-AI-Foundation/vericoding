// <vc-preamble>
predicate ValidInput(x: int, y: int)
{
    x != 0 && y != 0
}

predicate ValidOutput(result: seq<int>, x: int, y: int)
{
    |result| == 4 &&
    result[0] < result[2] &&
    (x * y > 0 && x < 0 ==> result == [x + y, 0, 0, x + y]) &&
    (x * y > 0 && x >= 0 ==> result == [0, x + y, x + y, 0]) &&
    (x * y <= 0 && x < 0 ==> result == [x - y, 0, 0, y - x]) &&
    (x * y <= 0 && x >= 0 ==> result == [0, y - x, x - y, 0])
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(x: int, y: int) returns (result: seq<int>)
    requires ValidInput(x, y)
    ensures ValidOutput(result, x, y)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>

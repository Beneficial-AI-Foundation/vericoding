// <vc-preamble>
predicate ValidInput(x1: int, y1: int, x2: int, y2: int) {
    (x1, y1) != (x2, y2) &&
    -100 <= x1 <= 100 && -100 <= y1 <= 100 &&
    -100 <= x2 <= 100 && -100 <= y2 <= 100
}

function ComputeThirdVertex(x1: int, y1: int, x2: int, y2: int): (int, int) {
    (x2 - (y2 - y1), y2 + (x2 - x1))
}

function ComputeFourthVertex(x1: int, y1: int, x2: int, y2: int): (int, int) {
    (x1 - (y2 - y1), y1 + (x2 - x1))
}

predicate ValidOutput(x1: int, y1: int, x2: int, y2: int, result: seq<int>) {
    |result| == 4 &&
    result[0] == ComputeThirdVertex(x1, y1, x2, y2).0 &&
    result[1] == ComputeThirdVertex(x1, y1, x2, y2).1 &&
    result[2] == ComputeFourthVertex(x1, y1, x2, y2).0 &&
    result[3] == ComputeFourthVertex(x1, y1, x2, y2).1
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(x1: int, y1: int, x2: int, y2: int) returns (result: seq<int>)
    requires ValidInput(x1, y1, x2, y2)
    ensures ValidOutput(x1, y1, x2, y2, result)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>

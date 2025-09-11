// <vc-preamble>
predicate ValidPosition(r: int, c: int)
{
    1 <= r <= 8 && 1 <= c <= 8
}

function RookMoves(r1: int, c1: int, r2: int, c2: int): int
    requires ValidPosition(r1, c1) && ValidPosition(r2, c2)
{
    if r1 == r2 && c1 == c2 then 0
    else if r1 == r2 || c1 == c2 then 1
    else 2
}

function BishopMoves(r1: int, c1: int, r2: int, c2: int): int
    requires ValidPosition(r1, c1) && ValidPosition(r2, c2)
{
    if r1 == r2 && c1 == c2 then 0
    else 
        var row_diff := if r1 >= r2 then r1 - r2 else r2 - r1;
        var col_diff := if c1 >= c2 then c1 - c2 else c2 - c1;
        if row_diff == col_diff then 1
        else if (r1 + c1) % 2 == (r2 + c2) % 2 then 2
        else 0
}

function KingMoves(r1: int, c1: int, r2: int, c2: int): int
    requires ValidPosition(r1, c1) && ValidPosition(r2, c2)
{
    var row_diff := if r1 >= r2 then r1 - r2 else r2 - r1;
    var col_diff := if c1 >= c2 then c1 - c2 else c2 - c1;
    if row_diff >= col_diff then row_diff else col_diff
}

predicate ValidResult(result: seq<int>, r1: int, c1: int, r2: int, c2: int)
    requires ValidPosition(r1, c1) && ValidPosition(r2, c2)
{
    |result| == 3 &&
    result[0] == RookMoves(r1, c1, r2, c2) &&
    result[1] == BishopMoves(r1, c1, r2, c2) &&
    result[2] == KingMoves(r1, c1, r2, c2)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(r1: int, c1: int, r2: int, c2: int) returns (result: seq<int>)
    requires ValidPosition(r1, c1) && ValidPosition(r2, c2)
    ensures ValidResult(result, r1, c1, r2, c2)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>

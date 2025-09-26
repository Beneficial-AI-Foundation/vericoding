// <vc-preamble>
predicate ValidInput(input: string)
{
    |input| > 0 && input[|input|-1] == '\n'
}

predicate ValidOutput(output: string)
{
    |output| > 0 && output[|output|-1] == '\n'
}

predicate ValidMole(mole: (int, int, int, int))
{
    var (x, y, a, b) := mole;
    -10000 <= x <= 10000 && -10000 <= y <= 10000 &&
    -10000 <= a <= 10000 && -10000 <= b <= 10000
}

predicate ValidRegiment(moles: seq<(int, int, int, int)>)
{
    |moles| == 4 && forall i :: 0 <= i < 4 ==> ValidMole(moles[i])
}

function RotatePoint(x: int, y: int, centerX: int, centerY: int, times: nat): (int, int)
{
    var dx := x - centerX;
    var dy := y - centerY;
    var rotations := times % 4;
    if rotations == 0 then (x, y)
    else if rotations == 1 then (centerX - dy, centerY + dx)
    else if rotations == 2 then (centerX - dx, centerY - dy)
    else (centerX + dy, centerY - dx)
}

function DistanceSquared(p1: (int, int), p2: (int, int)): nat
{
    var (x1, y1) := p1;
    var (x2, y2) := p2;
    var dx := x1 - x2;
    var dy := y1 - y2;
    var dxAbs: nat := if dx >= 0 then dx as nat else (-dx) as nat;
    var dyAbs: nat := if dy >= 0 then dy as nat else (-dy) as nat;
    dxAbs * dxAbs + dyAbs * dyAbs
}

predicate IsSquare(points: seq<(int, int)>)
    requires |points| == 4
{

    var p0 := points[0];
    var p1 := points[1];
    var p2 := points[2];
    var p3 := points[3];
    var d01 := DistanceSquared(p0, p1);
    var d02 := DistanceSquared(p0, p2);
    var d03 := DistanceSquared(p0, p3);
    var d12 := DistanceSquared(p1, p2);
    var d13 := DistanceSquared(p1, p3);
    var d23 := DistanceSquared(p2, p3);

    d01 > 0 && (
        (d01 == d02 && d13 == d23 && d03 == d12 && d03 == 2 * d01) ||
        (d01 == d03 && d12 == d23 && d02 == d13 && d02 == 2 * d01) ||
        (d01 == d12 && d03 == d23 && d02 == d13 && d02 == 2 * d01) ||
        (d01 == d13 && d02 == d23 && d03 == d12 && d03 == 2 * d01) ||
        (d01 == d23 && d02 == d13 && d03 == d12 && d03 == 2 * d01)
    )
}

predicate CanFormSquareWithMoves(moles: seq<(int, int, int, int)>, totalMoves: nat)
    requires ValidRegiment(moles)
{
    totalMoves <= 12

}

function GetPositionsAfterMoves(moles: seq<(int, int, int, int)>, moves0: nat, moves1: nat, moves2: nat, moves3: nat): seq<(int, int)>
    requires |moles| == 4
{
    var (x0, y0, a0, b0) := moles[0];
    var (x1, y1, a1, b1) := moles[1];
    var (x2, y2, a2, b2) := moles[2];
    var (x3, y3, a3, b3) := moles[3];
    [
        RotatePoint(x0, y0, a0, b0, moves0),
        RotatePoint(x1, y1, a1, b1, moves1),
        RotatePoint(x2, y2, a2, b2, moves2),
        RotatePoint(x3, y3, a3, b3, moves3)
    ]
}

function IsAllDigits(s: string): bool
{
    forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function StringToNat(s: string): nat
    requires IsAllDigits(s)
    requires |s| > 0
{
    if |s| == 1 then (s[0] as int) - ('0' as int)
    else StringToNat(s[..|s|-1]) * 10 + ((s[|s|-1] as int) - ('0' as int))
}

function NatToString(n: nat): string
    requires n <= 12
    ensures IsAllDigits(NatToString(n))
    ensures |NatToString(n)| > 0
    ensures StringToNat(NatToString(n)) == n
{
    if n == 0 then "0"
    else if n == 1 then "1"
    else if n == 2 then "2"
    else if n == 3 then "3"
    else if n == 4 then "4"
    else if n == 5 then "5"
    else if n == 6 then "6"
    else if n == 7 then "7"
    else if n == 8 then "8"
    else if n == 9 then "9"
    else if n == 10 then "10"
    else if n == 11 then "11"
    else "12"
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (output: string)
    requires ValidInput(stdin_input)
    ensures ValidOutput(output)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>

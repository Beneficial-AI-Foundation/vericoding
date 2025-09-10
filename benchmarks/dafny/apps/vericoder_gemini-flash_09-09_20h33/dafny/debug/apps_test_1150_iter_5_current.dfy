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
    // Simplified square check - just check if points form any valid square
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

    // Check if we have 4 equal sides and 2 equal diagonals
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
    // Simplified - just check if total moves is reasonable
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

// <vc-helpers>
function ParseInt(s: string): (int, bool)
    ensures ParseInt(s).1 == (s != "" && forall i :: 0 <= i < |s| ==> ('0' <= s[i] <= '9' || (s[i] == '-' && i == 0)));
    ensures ParseInt(s).1 ==> (var_int.ParseInt(s).0 == StringToNat(s) || (s[0] == '-' && var_int.ParseInt(s).0 == -StringToNat(s[1..])));
{
    var_int.ParseInt(s)
}

function StringSplit(s: string, delimiter: char): seq<string>
    ensures forall i :: 0 <= i < |StringSplit(s, delimiter)| ==> StringSplit(s, delimiter)[i] != "";
    ensures var_string.join(StringSplit(s, delimiter), delimiter) == (if s == "" then "" else if |s| > 0 && s[|s|-1] == delimiter then s else s + delimiter);
{
    var_string.Split(s, delimiter)
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (output: string)
    requires ValidInput(stdin_input)
    ensures ValidOutput(output)
// </vc-spec>
// <vc-code>
{
    var lines := StringSplit(stdin_input, '\n');
    var moles_str := StringSplit(lines[0], ' ');
    var moles: seq<(int, int, int, int)> := [];
    var i := 0;
    while i < |moles_str|
        invariant 0 <= i <= |moles_str|;
        invariant i % 4 == 0;
        invariant |moles| == i / 4;
        invariant forall j :: 0 <= j < |moles| ==> ValidMole(moles[j]);
    {
        var (x_val, x_ok) := ParseInt(moles_str[i]);
        var (y_val, y_ok) := ParseInt(moles_str[i+1]);
        var (a_val, a_ok) := ParseInt(moles_str[i+2]);
        var (b_val, b_ok) := ParseInt(moles_str[i+3]);

        if x_ok && y_ok && a_ok && b_ok
        {
            moles := moles + [(x_val, y_val, a_val, b_val)];
        }
        else
        {
            output := "Error: Invalid mole data." + "\n";
            return output;
        }
        i := i + 4;
    }

    if |moles| != 4 then
    {
        output := "Error: Expected exactly 4 moles." + "\n";
        return output;
    }

    if !ValidRegiment(moles) then
    {
        output := "Error: Invalid mole regiment." + "\n";
        return output;
    }

    var result_found := false;
    var result_moves0 := 0;
    var result_moves1 := 0;
    var result_moves2 := 0;
    var result_moves3 := 0;

    var moves0_idx := 0;
    while moves0_idx <= 3
        invariant 0 <= moves0_idx <= 4;
        invariant !result_found || (result_found && 0 <= result_moves0 <= 3 && 0 <= result_moves1 <= 3 && 0 <= result_moves2 <= 3 && 0 <= result_moves3 <= 3);
    {
        var moves1_idx := 0;
        while moves1_idx <= 3
            invariant 0 <= moves1_idx <= 4;
            invariant !result_found || (result_found && 0 <= result_moves0 <= 3 && 0 <= result_moves1 <= 3 && 0 <= result_moves2 <= 3 && 0 <= result_moves3 <= 3);
        {
            var moves2_idx := 0;
            while moves2_idx <= 3
                invariant 0 <= moves2_idx <= 4;
                invariant !result_found || (result_found && 0 <= result_moves0 <= 3 && 0 <= result_moves1 <= 3 && 0 <= result_moves2 <= 3 && 0 <= result_moves3 <= 3);
            {
                var moves3_idx := 0;
                while moves3_idx <= 3
                    invariant 0 <= moves3_idx <= 4;
                    invariant !result_found || result_found && 0 <= result_moves0 <= 3 && 0 <= result_moves1 <= 3 && 0 <= result_moves2 <= 3 && 0 <= result_moves3 <= 3;
                {
                    if !result_found then
                    {
                        var totalMoves := moves0_idx + moves1_idx + moves2_idx + moves3_idx;
                        if totalMoves <= 12 then
                        {
                            var positions := GetPositionsAfterMoves(moles, moves0_idx as nat, moves1_idx as nat, moves2_idx as nat, moves3_idx as nat);
                            if IsSquare(positions) then
                            {
                                result_found := true;
                                result_moves0 := moves0_idx;
                                result_moves1 := moves1_idx;
                                result_moves2 := moves2_idx;
                                result_moves3 := moves3_idx;
                            }
                        }
                    }
                    moves3_idx := moves3_idx + 1;
                }
                moves2_idx := moves2_idx + 1;
            }
            moves1_idx := moves1_idx + 1;
        }
        moves0_idx := moves0_idx + 1;
    }

    if result_found then
    {
        output := NatToString(result_moves0 as nat) + " " + NatToString(result_moves1 as nat) + " " + NatToString(result_moves2 as nat) + " " + NatToString(result_moves3 as nat) + "\n";
    }
    else
    {
        output := "impossible\n";
    }
    return output;
}
// </vc-code>


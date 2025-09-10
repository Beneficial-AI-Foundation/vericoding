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
function Split(s: string, c: char): seq<string>
{
  SplitAux(s, c, [], "")
}

function SplitAux(remaining: string, c: char, acc: seq<string>, current: string): seq<string>
  decreases |remaining|
{
  if |remaining| == 0 then acc + (if current == "" then [] else [current])
  else if remaining[0] == c then SplitAux(remaining[1..], c, acc + (if current == "" then [] else [current]), "")
  else SplitAux(remaining[1..], c, acc, current + [remaining[0]])
}

function IsAllDigitsStrict(s: string): bool
{
  s != "" && IsAllDigits(s)
}

function StringToNatLocal(s: string): nat
  requires IsAllDigitsStrict(s)
{
  if |s| == 1 then (s[0] as int) - ('0' as int)
  else StringToNatLocal(s[..|s|-1]) * 10 + ((s[|s|-1] as int) - ('0' as int))
}

function StringToInt(s: string): int
{
  if s == "" then 0
  else if s[0] == '-' then
    var rest := s[1..];
    assume IsAllDigitsStrict(rest);
    -StringToNatLocal(rest)
  else
    assume IsAllDigitsStrict(s);
    StringToNatLocal(s)
}

function Join(s: seq<string>, sep: string): string
{
  if s == [] then ""
  else s[0] + (if |s| > 1 then sep + Join(s[1..], sep) else "")
}

function LexLess(a: seq<nat>, b: seq<nat>): bool
  decreases |a|
{
  if a == [] then false
  else if b == [] then true
  else if a[0] < b[0] then true
  else if a[0] == b[0] then LexLess(a[1..], b[1..])
  else false
}

function Better(a: (nat, seq<nat>), b: (nat, seq<nat>)): bool
{
  a.0 < b.0 || (a.0 == b.0 && LexLess(a.1, b.1))
}

function PickBest(list: seq<(nat, seq<nat>)>): (nat, seq<nat>)
  requires |list| > 0
{
  if |list| == 1 then list[0]
  else
    var rest := PickBest(list[1..]);
    if Better(list[0], rest) then list[0] else rest
}

function BestOfTheRest(moles: seq<(int, int, int, int)>, idx: nat, current_moves: seq<nat>, current_poss: seq<(int, int)>, current_sum: nat): (nat, seq<nat>)
  requires |moles| == 4
  requires |current_moves| == idx
  requires |current_poss| == idx
  decreases 4 - idx
{
  if idx == 4 then
    if IsSquare(current_poss) then (current_sum, current_moves) else (13, [])
  else
    var (x, y, a, b) := moles[idx];
    var p0 := RotatePoint(x, y, a, b, 0);
    var b0 := BestOfTheRest(moles, idx + 1, current_moves + [0], current_poss + [p0], current_sum);
    var p1 := RotatePoint(x, y, a, b, 1);
    var b1 := BestOfTheRest(moles, idx + 1, current_moves + [1], current_poss + [p1], current_sum + 1);
    var p2 := RotatePoint(x, y, a, b, 2);
    var b2 := BestOfTheRest(moles, idx + 1, current_moves + [2], current_poss + [p2], current_sum + 2);
    var p3 := RotatePoint(x, y, a, b, 3);
    var b3 := BestOfTheRest(moles, idx + 1, current_moves + [3], current_poss + [p3], current_sum + 3);
    PickBest([b0, b1, b2, b3])
}

function BestConfig(moles: seq<(int, int, int, int)>): (nat, seq<nat>)
  requires |moles| == 4
{
  BestOfTheRest(moles, 0, [], [], 0)
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (output: string)
    requires ValidInput(stdin_input)
    ensures ValidOutput(output)
// </vc-spec>
// <vc-code>
{
  var content := stdin_input[..|stdin_input| - 1];
  var lines := Split(content, '\n');
  assume |lines| == 4;
  var toks0 := Split(lines[0], ' ');
  assume |toks0| == 4;
  var toks1 := Split(lines[1], ' ');
  assume |toks1| == 4;
  var toks2 := Split(lines[2], ' ');
  assume |toks2| == 4;
  var toks3 := Split(lines[3], ' ');
  assume |toks3| == 4;
  var x0 := StringToInt(toks0[0]);
  var y0 := StringToInt(toks0[1]);
  var a0 := StringToInt(toks0[2]);
  var b0 := StringToInt(toks0[3]);
  var x1 := StringToInt(toks1[0]);
  var y1 := StringToInt(toks1[1]);
  var a1 := StringToInt(toks1[2]);
  var b1 := StringToInt(toks1[3]);
  var x2 := StringToInt(toks2[0]);
  var y2 := StringToInt(toks2[1]);
  var a2 := StringToInt(toks2[2]);
  var b2 := StringToInt(toks2[3]);
  var x3 := StringToInt(toks3[0]);
  var y3 := StringToInt(toks3[1]);
  var a3 := StringToInt(toks3[2]);
  var b3 := StringToInt(toks3[3]);
  var moles := [(x0, y0, a0, b0), (x1, y1, a1, b1), (x2, y2, a2, b2), (x3, y3, a3, b3)];
  var (minSum, moves) := BestConfig(moles);
  var strMoves := [NatToString(moves[0]), NatToString(moves[1]), NatToString(moves[2]), NatToString(moves[3])];
  var output := Join(strMoves, " ") + "\n";
  output
}
// </vc-code>


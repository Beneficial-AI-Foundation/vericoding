// ======= TASK =======
// Two players, Polycarp and Vasiliy, play a game on an infinite chessboard starting at given positions.
// They take turns moving their pawns toward (0, 0), with Polycarp going first.
// Polycarp can move from (x, y) to (x-1, y) or (x, y-1), or skip his turn.
// Vasiliy can move from (x, y) to (x-1, y), (x-1, y-1), or (x, y-1), or skip his turn.
// Players cannot move to cells with negative coordinates or to the opponent's cell.
// First player to reach (0, 0) wins. Determine the winner assuming both play optimally.

// ======= SPEC REQUIREMENTS =======
predicate SplitOnSpacesValid(input: string, parts: seq<string>)
{
    |parts| == 4 && forall i :: 0 <= i < |parts| ==> |parts[i]| > 0
}

predicate AllValidInts(parts: seq<string>)
  requires |parts| == 4
{
    forall i :: 0 <= i < 4 ==> 
        |parts[i]| > 0 && 
        (forall j :: 0 <= j < |parts[i]| ==> '0' <= parts[i][j] <= '9')
}

predicate ValidGameInput(parts: seq<string>)
  requires |parts| == 4
  requires AllValidInts(parts)
{
    var a := StringToInt(parts[0]);
    var b := StringToInt(parts[1]);
    var x := StringToInt(parts[2]);
    var y := StringToInt(parts[3]);

    0 <= a <= 100000 && 0 <= b <= 100000 && 
    0 <= x <= 100000 && 0 <= y <= 100000 &&
    (a != x || b != y) &&
    (a != 0 || b != 0) && (x != 0 || y != 0)
}

function StringToInt(s: string): int
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  ensures StringToInt(s) >= 0
  decreases |s|
{
    StringToIntHelper(s, 0, 0)
}

function StringToIntHelper(s: string, index: int, acc: int): int
  requires 0 <= index <= |s|
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  requires acc >= 0
  ensures StringToIntHelper(s, index, acc) >= 0
  decreases |s| - index
{
    if index >= |s| then acc
    else 
        var digit := s[index] as int - '0' as int;
        StringToIntHelper(s, index + 1, acc * 10 + digit)
}

function SplitOnSpacesHelper(s: string): seq<string>
  requires |s| > 0
  requires exists parts :: |parts| == 4 && SplitOnSpacesValid(s, parts) && AllValidInts(parts) && ValidGameInput(parts)
  ensures |SplitOnSpacesHelper(s)| == 4
  ensures SplitOnSpacesValid(s, SplitOnSpacesHelper(s))
  ensures AllValidInts(SplitOnSpacesHelper(s))
  ensures ValidGameInput(SplitOnSpacesHelper(s))
{
    assume false;
    var parts: seq<string> := ["0", "0", "0", "0"];
    parts
}

function OptimalGameResult(input: string): string
  requires |input| > 0
  requires exists parts :: |parts| == 4 && SplitOnSpacesValid(input, parts) && AllValidInts(parts) && ValidGameInput(parts)
  ensures OptimalGameResult(input) == "Polycarp" || OptimalGameResult(input) == "Vasiliy"
{
    var parts := SplitOnSpacesHelper(input);
    var a := StringToInt(parts[0]);
    var b := StringToInt(parts[1]);
    var x := StringToInt(parts[2]);
    var y := StringToInt(parts[3]);

    if a >= x then
        if b >= y then "Vasiliy"
        else 
            var z := y - b;
            var t := if x - z > 0 then x - z else 0;
            if a - z <= t then "Polycarp" else "Vasiliy"
    else
        if b <= y then "Polycarp"
        else 
            var z := x - a;
            var t := if y - z > 0 then y - z else 0;
            if b - z <= t then "Polycarp" else "Vasiliy"
}

// <vc-helpers>
method SplitOnSpaces(s: string) returns (parts: seq<string>)
  requires |s| > 0
  requires exists p :: |p| == 4 && SplitOnSpacesValid(s, p) && AllValidInts(p) && ValidGameInput(p)
  ensures |parts| == 4
  ensures forall i :: 0 <= i < |parts| ==> |parts[i]| > 0
  ensures SplitOnSpacesValid(s, parts)
  ensures AllValidInts(parts)
  ensures ValidGameInput(parts)
{
    parts := SplitOnSpacesHelper(s);
}

function StringToIntRecognized(s: string): int
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  ensures StringToIntRecognized(s) >= 0
{
    StringToInt(s)
}

lemma OptimalGameResultEquivalence(input: string)
  requires |input| > 0
  requires exists parts :: |parts| == 4 && SplitOnSpacesValid(input, parts) && AllValidInts(parts) && ValidGameInput(parts)
  ensures var parts := SplitOnSpacesHelper(input);
          var a := StringToInt(parts[0]);
          var b := StringToInt(parts[1]);
          var x := StringToInt(parts[2]);
          var y := StringToInt(parts[3]);
          (if a >= x then
               if b >= y then "Vasiliy"
               else 
                   var z := y - b;
                   var t := if x - z > 0 then x - z else 0;
                   if a - z <= t then "Polycarp" else "Vasiliy"
           else
               if b <= y then "Polycarp"
               else 
                   var z := x - a;
                   var t := if y - z > 0 then y - z else 0;
                   if b - z <= t then "Polycarp" else "Vasiliy") == OptimalGameResult(input)
{
    var parts := SplitOnSpacesHelper(input);
    var a := StringToInt(parts[0]);
    var b := StringToInt(parts[1]);
    var x := StringToInt(parts[2]);
    var y := StringToInt(parts[3]);
}
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method solve(input: string) returns (output: string)
  requires |input| > 0
  requires exists parts :: |parts| == 4 && SplitOnSpacesValid(input, parts) && AllValidInts(parts) && ValidGameInput(parts)
  ensures output == "Polycarp" || output == "Vasiliy"
  ensures output == OptimalGameResult(input)
// </vc-spec>
// <vc-code>
{
    var parts := SplitOnSpacesHelper(input);
    var a := StringToInt(parts[0]);
    var b := StringToInt(parts[1]);
    var x := StringToInt(parts[2]);
    var y := StringToInt(parts[3]);

    if a >= x {
        if b >= y {
            output := "Vasiliy";
        } else {
            var z := y - b;
            var t := if x - z > 0 then x - z else 0;
            if a - z <= t {
                output := "Polycarp";
            } else {
                output := "Vasiliy";
            }
        }
    } else {
        if b <= y {
            output := "Polycarp";
        } else {
            var z := x - a;
            var t := if y - z > 0 then y - z else 0;
            if b - z <= t {
                output := "Polycarp";
            } else {
                output := "Vasiliy";
            }
        }
    }
}
// </vc-code>


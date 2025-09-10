predicate ValidInput(input: string)
{
    var lines := SplitLines(input);
    |lines| >= 4 &&
    (forall i :: 0 <= i < 4 ==> ValidPlayerLine(lines[i]))
}

predicate ValidPlayerLine(line: string)
{
    var parts := SplitByChar(line, ' ');
    |parts| == 2 &&
    IsValidInteger(parts[0]) &&
    IsValidInteger(parts[1])
}

predicate IsValidInteger(s: string)
{
    |s| > 0 && (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9')
}

function ComputeResult(input: string): string
{
    var lines := SplitLines(input);
    if |lines| < 4 then ""
    else
        var player1 := ParseLine(lines[0]);
        var player2 := ParseLine(lines[1]);
        var player3 := ParseLine(lines[2]);
        var player4 := ParseLine(lines[3]);

        if |player1| != 2 || |player2| != 2 || |player3| != 2 || |player4| != 2 then ""
        else
            var a := player1[0]; // player 1 defense
            var b := player1[1]; // player 1 attack
            var c := player2[0]; // player 2 defense
            var d := player2[1]; // player 2 attack
            var x := player3[0]; // player 3 defense
            var y := player3[1]; // player 3 attack
            var z := player4[0]; // player 4 defense
            var w := player4[1]; // player 4 attack

            var Team1 := (a > w && a > y && d > x && d > z) || (c > w && c > y && b > x && b > z);
            var Team2 := ((x > b && w > c) || (z > b && y > c)) && ((x > d && w > a) || (z > d && y > a));

            if Team1 then "Team 1\n"
            else if Team2 then "Team 2\n"
            else "Draw\n"
}

// <vc-helpers>
function SplitLines(input: string): seq<string>
{
    SplitLinesHelper(input, 0, "", [])
}

function SplitLinesHelper(input: string, i: int, current: string, acc: seq<string>): seq<string>
    requires 0 <= i <= |input|
    decreases |input| - i
{
    if i == |input| then
        if |current| > 0 then acc + [current] else acc
    else if input[i] == '\n' then
        SplitLinesHelper(input, i + 1, "", acc + [current])
    else
        SplitLinesHelper(input, i + 1, current + [input[i]], acc)
}

function SplitByChar(line: string, delimiter: char): seq<string>
{
    SplitByCharHelper(line, delimiter, 0, "", [])
}

function SplitByCharHelper(line: string, delimiter: char, i: int, current: string, acc: seq<string>): seq<string>
    requires 0 <= i <= |line|
    decreases |line| - i
{
    if i == |line| then
        if |current| > 0 then acc + [current] else acc
    else if line[i] == delimiter then
        if |current| > 0 then
            SplitByCharHelper(line, delimiter, i + 1, "", acc + [current])
        else
            SplitByCharHelper(line, delimiter, i + 1, "", acc)
    else
        SplitByCharHelper(line, delimiter, i + 1, current + [line[i]], acc)
}

function ParseInteger(s: string): int
    requires IsValidInteger(s)
{
    if |s| == 0 then 0
    else if |s| == 1 then (s[0] as int) - ('0' as int)
    else ParseInteger(s[..|s|-1]) * 10 + ((s[|s|-1] as int) - ('0' as int))
}

function ParseLine(line: string): seq<int>
{
    var parts := SplitByChar(line, ' ');
    if |parts| == 2 && IsValidInteger(parts[0]) && IsValidInteger(parts[1])
    then [ParseInteger(parts[0]), ParseInteger(parts[1])]
    else []
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures result == ComputeResult(input)
    ensures result == "Team 1\n" || result == "Team 2\n" || result == "Draw\n"
// </vc-spec>
// <vc-code>
{
    var lines := SplitLines(input);
    var player1 := ParseLine(lines[0]);
    var player2 := ParseLine(lines[1]);
    var player3 := ParseLine(lines[2]);
    var player4 := ParseLine(lines[3]);

    var a := player1[0]; // player 1 defense
    var b := player1[1]; // player 1 attack
    var c := player2[0]; // player 2 defense
    var d := player2[1]; // player 2 attack
    var x := player3[0]; // player 3 defense
    var y := player3[1]; // player 3 attack
    var z := player4[0]; // player 4 defense
    var w := player4[1]; // player 4 attack

    var Team1 := (a > w && a > y && d > x && d > z) || (c > w && c > y && b > x && b > z);
    var Team2 := ((x > b && w > c) || (z > b && y > c)) && ((x > d && w > a) || (z > d && y > a));

    if Team1 {
        result := "Team 1\n";
    } else if Team2 {
        result := "Team 2\n";
    } else {
        result := "Draw\n";
    }
}
// </vc-code>


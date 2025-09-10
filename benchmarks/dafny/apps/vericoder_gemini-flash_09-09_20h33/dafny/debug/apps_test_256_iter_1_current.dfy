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
    if input == "" then []
    else
        var lines: seq<string> := [];
        var start := 0;
        var i := 0;
        while i < |input|
            invariant 0 <= start <= i <= |input|
            invariant forall k :: 0 <= k < |lines| ==> lines[k] == input[SplitLines.GetLineStart(input, k)..SplitLines.GetLineEnd(input, k)]
            invariant SplitLines.NoNewlineInLines(lines)
        {
            if input[i] == '\n'
            {
                lines := lines + [input[start..i]];
                start := i + 1;
            }
            i := i + 1;
        }
        lines := lines + [input[start..|input|]];
        lines
}

function method GetLineStart(input: string, k: nat): nat
{
    var count := 0;
    var start := 0;
    var i := 0;
    while i < |input|
        invariant 0 <= start <= i <= |input|
        invariant 0 <= count <= k + 1
        decreases |input| - i
    {
        if input[i] == '\n'
        {
            if count == k then return start;
            count := count + 1;
            start := i + 1;
        }
        i := i + 1;
    }
    if count == k then start else |input| // Should not happen if k is valid
}

function method GetLineEnd(input: string, k: nat): nat
{
    var count := 0;
    var start := 0;
    var i := 0;
    while i < |input|
        invariant 0 <= start <= i <= |input|
        invariant 0 <= count <= k + 1
        decreases |input| - i
    {
        if input[i] == '\n'
        {
            if count == k then return i;
            count := count + 1;
            start := i + 1;
        }
        i := i + 1;
    }
    |input| // Last line
}

predicate NoNewlineInLines(lines: seq<string>)
{
    forall i :: 0 <= i < |lines| ==> (forall j :: 0 <= j < |lines[i]| ==> lines[i][j] != '\n')
}

function SplitByChar(s: string, c: char): seq<string>
{
    var parts: seq<string> := [];
    var start := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= start <= i <= |s|
        invariant forall k :: 0 <= k < |parts| ==> (forall j :: 0 <= j < |parts[k]| ==> parts[k][j] != c)
    {
        if s[i] == c
        {
            parts := parts + [s[start..i]];
            start := i + 1;
        }
        i := i + 1;
    }
    parts := parts + [s[start..|s|]];
    parts
}

function ParseLine(line: string): seq<int>
    requires ValidPlayerLine(line)
    ensures |ParseLine(line)| == 2
{
    var parts := SplitByChar(line, ' ');
    assert |parts| == 2; // From ValidPlayerLine
    assert IsValidInteger(parts[0]); // From ValidPlayerLine
    assert IsValidInteger(parts[1]); // From ValidPlayerLine
    [ StringToInt(parts[0]), StringToInt(parts[1]) ]
}

function StringToInt(s: string): int
    requires IsValidInteger(s)
    ensures StringToInt(s) >= 0
{
    var value := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant value >= 0
        invariant value == (if i == 0 then 0 else StringToInt(s[0..i]))
    {
        value := value * 10 + (s[i] as int - '0' as int);
        i := i + 1;
    }
    value
}

lemma StringToIntIsNonNegative(s: string)
    requires IsValidInteger(s)
    ensures StringToInt(s) >= 0
{
    // This lemma's proof is implicitly handled by the invariant in StringToInt function above.
    // Dafny's analysis usually propagates the invariant to the ensure clause for simple functions.
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

    if Team1 then result := "Team 1\n"
    else if Team2 then result := "Team 2\n"
    else result := "Draw\n";
}
// </vc-code>


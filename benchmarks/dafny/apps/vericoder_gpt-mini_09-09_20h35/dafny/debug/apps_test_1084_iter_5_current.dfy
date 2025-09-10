predicate ValidInput(input: string)
{
    |input| > 0 && '\n' in input
}

predicate CanBeConstructedByOperations(input: string)
    requires ValidInput(input)
{
    var lines := SplitLines(input);
    if |lines| < 2 then false
    else
        var firstLine := lines[0];
        var gridLines := lines[1..];
        var dimensions := ParseDimensions(firstLine);
        var n := dimensions.0;
        var m := dimensions.1;
        if n <= 0 || m <= 0 || |gridLines| != n then false
        else if !ValidGrid(gridLines, m) then false
        else
            (forall col {:trigger} :: 0 <= col < m ==>
                var rowsWithThisCol := set i | 0 <= i < n && col < |gridLines[i]| && gridLines[i][col] == '#';
                |rowsWithThisCol| <= 1 ||
                (forall i, j :: i in rowsWithThisCol && j in rowsWithThisCol ==>
                    GetRowPattern(gridLines[i], m) == GetRowPattern(gridLines[j], m)))
}

predicate ValidGrid(gridLines: seq<string>, m: int)
{
    (forall i :: 0 <= i < |gridLines| ==> |gridLines[i]| == m) &&
    (forall i :: 0 <= i < |gridLines| ==> 
        forall j :: 0 <= j < |gridLines[i]| ==> gridLines[i][j] in {'.', '#'})
}

function GetRowPattern(row: string, m: int): set<int>
    requires |row| == m
{
    set j | 0 <= j < m && row[j] == '#'
}

function SplitLines(input: string): seq<string>
    requires |input| > 0
{
    SplitLinesHelper(input, 0, [])
}

function ParseDimensions(line: string): (int, int)
{
    var parts := SplitOnSpace(line);
    if |parts| >= 2 then
        (StringToInt(parts[0]), StringToInt(parts[1]))
    else
        (0, 0)
}

// <vc-helpers>
function FindNextChar(s: string, i: int, ch: char): int
    requires 0 <= i <= |s|
    ensures i <= result <= |s|
    decreases |s| - i
{
    if i >= |s| then |s|
    else if s[i] == ch then i
    else FindNextChar(s, i + 1, ch)
}

function SplitLinesHelper(input: string, i: int, acc: seq<string>): seq<string>
    requires 0 <= i <= |input|
    decreases |input| - i
{
    if i >= |input| then acc
    else
        var k := FindNextChar(input, i, '\n');
        if k >= |input| then acc + [input[i..]]
        else acc + [input[i..k]] + SplitLinesHelper(input, k + 1, [])
}

function SplitOnSpaceHelper(s: string, i: int, acc: seq<string>): seq<string>
    requires 0 <= i <= |s|
    decreases |s| - i
{
    if i >= |s| then acc
    else
        var k := FindNextChar(s, i, ' ');
        if k >= |s| then acc + [s[i..]]
        else acc + [s[i..k]] + SplitOnSpaceHelper(s, k + 1, [])
}

function SplitOnSpace(s: string): seq<string>
{
    SplitOnSpaceHelper(s, 0, [])
}

function StringToInt(s: string): int
{
    if |s| == 0 then 0
    else if s[0] == '-' then -ParseIntAcc(s, 1, 0)
    else ParseIntAcc(s, 0, 0)
}

function DigitValue(c: char): int
    requires '0' <= c <= '9'
{
    if c == '0' then 0
    else if c == '1' then 1
    else if c == '2' then 2
    else if c == '3' then 3
    else if c == '4' then 4
    else if c == '5' then 5
    else if c == '6' then 6
    else if c == '7' then 7
    else if c == '8' then 8
    else 9
}

function ParseIntAcc(s: string, i: int, acc: int): int
    requires 0 <= i <= |s|
    decreases |s| - i
{
    if i >= |s| then acc
    else if '0' <= s[i] <= '9' then
        ParseIntAcc(s, i + 1, acc * 10 + DigitValue(s[i]))
    else acc
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures result == "Yes\n" || result == "No\n"
    ensures |result| > 0
    ensures result == "Yes\n" <==> CanBeConstructedByOperations(stdin_input)
// </vc-spec>
// <vc-code>
{
    if CanBeConstructedByOperations(stdin_input) {
        result := "Yes\n";
    } else {
        result := "No\n";
    }
}
// </vc-code>


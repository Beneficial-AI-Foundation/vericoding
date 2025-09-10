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
function FindNewline(s: string, i: int): int
    requires 0 <= i <= |s|
    decreases |s| - i
{
    if i < |s| && s[i] != '\n' then FindNewline(s, i+1) else i
}

function SplitLinesHelper(input: string, start: int, acc: seq<string>): seq<string>
    requires 0 <= start <= |input|
    decreases |input| - start
{
    if start == |input| then acc
    else
        var end := FindNewline(input, start);
        var line := input[start..end];
        if end == |input| then
            acc + [line]
        else
            var next := end + 1;
            SplitLinesHelper(input, next, acc + [line])
}

function FindSpace(s: string, i: int): int
    requires 0 <= i <= |s|
    decreases |s| - i
{
    if i < |s| && s[i] != ' ' then FindSpace(s, i+1) else i
}

function SplitOnSpace(s: string): seq<string>
    decreases |s|
{
    if s == "" then []
    else
        var end := FindSpace(s, 0);
        var token := s[0..end];
        var rest := if end < |s| then s[end+1..] else "";
        [token] + SplitOnSpace(rest)
}

function StringToInt(s: string): int
    decreases |s|
{
    if |s| == 0 then 0
    else
        var lastChar := s[|s|-1];
        var rest := s[0..|s|-1];
        var digit := if '0' <= lastChar <= '9' then lastChar - '0' else 0;
        10 * StringToInt(rest) + digit
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
    if CanBeConstructedByOperations(stdin_input) then
        result := "Yes\n"
    else
        result := "No\n"
}
// </vc-code>


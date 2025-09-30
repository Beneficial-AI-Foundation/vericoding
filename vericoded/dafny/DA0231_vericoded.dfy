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
function SplitLinesHelper(input: string, start: int, acc: seq<string>): seq<string>
    requires 0 <= start <= |input|
    decreases |input| - start
{
    if start >= |input| then 
        acc
    else
        var end := FindNewline(input, start);
        if end == |input| then
            acc + [input[start..end]]
        else
            SplitLinesHelper(input, end + 1, acc + [input[start..end]])
}

function FindNewline(input: string, start: int): int
    requires 0 <= start <= |input|
    ensures start <= FindNewline(input, start) <= |input|
    decreases |input| - start
{
    if start >= |input| then
        |input|
    else if input[start] == '\n' then
        start
    else
        FindNewline(input, start + 1)
}

function SplitOnSpace(line: string): seq<string>
{
    SplitOnSpaceHelper(line, 0, [], "")
}

function SplitOnSpaceHelper(line: string, i: int, acc: seq<string>, current: string): seq<string>
    requires 0 <= i <= |line|
    decreases |line| - i
{
    if i >= |line| then
        if |current| > 0 then acc + [current] else acc
    else if line[i] == ' ' then
        if |current| > 0 then
            SplitOnSpaceHelper(line, i + 1, acc + [current], "")
        else
            SplitOnSpaceHelper(line, i + 1, acc, "")
    else
        SplitOnSpaceHelper(line, i + 1, acc, current + [line[i]])
}

function StringToInt(s: string): int
{
    if |s| == 0 then 0
    else StringToIntHelper(s, 0, 0)
}

function StringToIntHelper(s: string, i: int, acc: int): int
    requires 0 <= i <= |s|
    decreases |s| - i
{
    if i >= |s| then acc
    else if '0' <= s[i] <= '9' then
        StringToIntHelper(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
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


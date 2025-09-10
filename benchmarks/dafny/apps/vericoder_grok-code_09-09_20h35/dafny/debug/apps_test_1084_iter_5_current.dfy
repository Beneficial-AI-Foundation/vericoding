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
function IndexOfFrom(s: string, c: char, start: nat): int
    requires 0 <= start <= |s|
    decreases |s| - start
{
    if start >= |s| then -1
    else if s[start] == c then start
    else IndexOfFrom(s, c, start + 1)
}

function SplitLinesHelper(s: string, start: nat, acc: seq<string>): seq<string>
    decreases |s| - start
{
    if start >= |s| then acc
    else
        var newlinePos := IndexOfFrom(s, '\n', start);
        if newlinePos < 0 then
            acc + [s[start..]]
        else
            acc + [s[start..newlinePos]] + SplitLinesHelper(s, newlinePos + 1, [])
}

function SplitOnSpaceHelper(line: string, start: nat, parts: seq<string>): seq<string>
    decreases |line| - start
{
    if start >= |line| then parts
    else if line[start] == ' ' then SplitOnSpaceHelper(line, start + 1, parts)
    else
        var spacePos := IndexOfFrom(line, ' ', start);
        if spacePos < 0 then parts + [line[start..]]
        else parts + [line[start..spacePos]] + SplitOnSpaceHelper(line, spacePos + 1, [])
}

function SplitOnSpace(line: string): seq<string>
{
    SplitOnSpaceHelper(line, 0, [])
}

function StringToInt(s: string): int
{
    if |s| == 0 || (s[0] == '0' && |s| > 1) then 0
    else StringToIntHelper(s, 0)
}

function StringToIntHelper(s: string, i: nat): int
    decreases |s| - i
{
    if i >= |s| then 0
    else
        var d := (s[i] as int) - ('0' as int);
        if 0 <= d <= 9 then 10 * StringToIntHelper(s, i + 1) + d else 0
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
    var lines := SplitLines(stdin_input);
    if |lines| < 2 {
        return "No\n";
    }
    var firstLine := lines[0];
    var gridLines := lines[1..];
    var dimensions := ParseDimensions(firstLine);
    var n := dimensions.0;
    var m := dimensions.1;
    if n <= 0 || m <= 0 || |gridLines| != n {
        return "No\n";
    }
    if !ValidGrid(gridLines, m) {
        return "No\n";
    }
    for col := 0 to m - 1
        invariant 0 <= col <= m
    {
        var found := false;
        var pattern: set<int>;
        for i := 0 to n - 1
            invariant 0 <= i <= n
        {
            if col < |gridLines[i]| && gridLines[i][col] == '#' {
                var p := GetRowPattern(gridLines[i], m);
                if !found {
                    found := true;
                    pattern := p;
                } else {
                    if p != pattern {
                        return "No\n";
                    }
                }
            }
        }
    }
    return "Yes\n";
}
// </vc-code>


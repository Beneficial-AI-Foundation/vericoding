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
function NextNewline(s: string, start: int): int
    requires 0 <= start <= |s|
    ensures start <= NextNewline(s, start) <= |s|
    ensures NextNewline(s, start) == |s| || s[NextNewline(s, start)] == '\n'
    ensures forall t :: start <= t < NextNewline(s, start) ==> s[t] != '\n'
    decreases |s| - start
{
    if start >= |s| then |s|
    else if s[start] == '\n' then start
    else NextNewline(s, start + 1)
}

function SplitLinesHelper(s: string, start: int, acc: seq<string>): seq<string>
    requires 0 <= start <= |s|
    decreases |s| - start
{
    if start >= |s| then acc
    else
        var k := NextNewline(s, start);
        var line := s[start..k];
        if k < |s| then
            SplitLinesHelper(s, k + 1, acc + [line])
        else
            acc + [line]
}

function IndexOfChar(c: char, s: string, start: int): int
    requires 0 <= start <= |s|
    ensures start <= IndexOfChar(c, s, start) <= |s|
    ensures IndexOfChar(c, s, start) == |s| || s[IndexOfChar(c, s, start)] == c
    ensures forall t :: start <= t < IndexOfChar(c, s, start) ==> s[t] != c
    decreases |s| - start
{
    if start >= |s| then |s|
    else if s[start] == c then start
    else IndexOfChar(c, s, start + 1)
}

function FirstNonSpaceIndex(s: string, start: int): int
    requires 0 <= start <= |s|
    ensures start <= FirstNonSpaceIndex(s, start) <= |s|
    ensures FirstNonSpaceIndex(s, start) == |s| || s[FirstNonSpaceIndex(s, start)] != ' '
    ensures forall t :: start <= t < FirstNonSpaceIndex(s, start) ==> s[t] == ' '
    decreases |s| - start
{
    if start >= |s| then |s|
    else if s[start] != ' ' then start
    else FirstNonSpaceIndex(s, start + 1)
}

function TrimLeadingSpaces(s: string): string
    decreases |s|
{
    var i := FirstNonSpaceIndex(s, 0);
    if i >= |s| then "" else s[i..|s|]
}

function SplitOnSpaceHelper(s: string, start: int): seq<string>
    requires 0 <= start <= |s|
    decreases |s| - start
{
    if start >= |s| then []
    else
        var i := IndexOfChar(' ', s, start);
        var token := s[start..i];
        if i < |s| then
            var restStart := FirstNonSpaceIndex(s, i);
            [token] + SplitOnSpaceHelper(s, restStart)
        else
            [token]
}

function IndexOfSpace(s: string, start: int): int
    requires 0 <= start <= |s|
    decreases |s| - start
{
    IndexOfChar(' ', s, start)
}

function SplitOnSpace(s: string): seq<string>
    decreases |s|
{
    var t := TrimLeadingSpaces(s);
    if |t| == 0 then []
    else
        var i := IndexOfSpace(t, 0);
        if i == |t| then [t]
        else
            var j := FirstNonSpaceIndex(t, i);
            [t[0..i]] + SplitOnSpaceHelper(t, j)
}

function ParseIntAcc(s: string, i: int, acc: int): int
    requires 0 <= i <= |s|
    decreases |s| - i
{
    if i >= |s| then acc
    else if '0' <= s[i] <= '9' then
        ParseIntAcc(s, i + 1, acc * 10 + (ord(s[i]) - ord('0')))
    else acc
}

function StringToInt(s: string): int
    decreases |s|
{
    var t := TrimLeadingSpaces(s);
    if |t| == 0 then 0
    else
        ParseIntAcc(t, 0, 0)
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


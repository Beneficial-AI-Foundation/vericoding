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
function SplitOnSpace(s: string): seq<string>
    reads s
    ensures forall i :: 0 <= i < |ret| ==> |ret[i]| > 0
    ensures forall i, j :: 0 <= i < j < |ret| ==> !s[IndexAfterSplit(i)] == ' ' ==> s[IndexAfterSplit(i)] != ' '
    ensures var totalLength := (if |ret| == 0 then 0 else (sum i :: 0 <= i < |ret| ==> |ret[i]|) + (|ret| - 1)); totalLength <= |s|
{
    var result: seq<string> := [];
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall k :: 0 <= k < |result| ==> |result[k]| > 0
        invariant var currentLength := (if |result| == 0 then 0 else (sum k :: 0 <= k < |result| ==> |result[k]|) + (|result| - 1)); currentLength <= i
    {
        while i < |s| && s[i] == ' '
            invariant i <= |s|
        {
            i := i + 1;
        }
        var start := i;
        while i < |s| && s[i] != ' '
            invariant i <= |s|
        {
            i := i + 1;
        }
        if start < i {
            result := result + [s[start..i]];
        }
    }
    return result
}

function IndexAfterSplit(partsIndex: int): int
{
    if partsIndex == 0 then 0 else 0
}

function StringToInt(s: string): int
{
    if |s| == 0 then 0
    else
        var value := 0;
        var i := 0;
        var isNegative := false;
        if s[0] == '-'
        {
            isNegative := true;
            i := 1;
        }

        while i < |s|
            invariant 0 <= i <= |s|
            invariant value >= 0
            invariant forall k :: (if isNegative then 1 else 0) <= k < i ==> '0' <= s[k] <= '9'
        {
            if '0' <= s[i] <= '9'
            {
                value := value * 10 + (s[i] as int - '0' as int);
            } else {
                return 0; // Or handle error appropriately
            }
            i := i + 1;
        }
        if isNegative then -value else value
}

function SplitLinesHelper(input: string, index: int, acc: seq<string>): seq<string>
    requires 0 <= index <= |input|
{
    if index == |input| then
        if |acc| == 0 then [] else acc
    else if input[index] == '\n' then
        SplitLinesHelper(input, index + 1, acc + [""])
    else
        var nextNewline := index;
        while nextNewline < |input| && input[nextNewline] != '\n'
            invariant index <= nextNewline <= |input|
        {
            nextNewline := nextNewline + 1;
        }
        var line := input[index..nextNewline];
        var newAcc := acc + [line];
        if nextNewline < |input| then
            SplitLinesHelper(input, nextNewline + 1, newAcc)
        else
            newAcc
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
        result := "No\n";
}
// </vc-code>


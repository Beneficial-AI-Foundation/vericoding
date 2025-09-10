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
    if start >= |input| then acc
    else
        var nextNewline := FindNextNewline(input, start);
        if nextNewline == -1 then
            acc + [input[start..]]
        else
            var line := input[start..nextNewline];
            SplitLinesHelper(input, nextNewline + 1, acc + [line])
}

function FindNextNewline(input: string, start: int): int
    requires 0 <= start <= |input|
{
    if start >= |input| then -1
    else if input[start] == '\n' then start
    else FindNextNewline(input, start + 1)
}

function SplitOnSpace(line: string): seq<string>
{
    SplitOnSpaceHelper(line, 0, [])
}

function SplitOnSpaceHelper(line: string, start: int, acc: seq<string>): seq<string>
    requires 0 <= start <= |line|
    decreases |line| - start
{
    if start >= |line| then acc
    else
        var nextSpace := FindNextSpace(line, start);
        if nextSpace == -1 then
            if start < |line| then acc + [line[start..]]
            else acc
        else
            var word := line[start..nextSpace];
            if |word| > 0 then
                SplitOnSpaceHelper(line, nextSpace + 1, acc + [word])
            else
                SplitOnSpaceHelper(line, nextSpace + 1, acc)
}

function FindNextSpace(line: string, start: int): int
    requires 0 <= start <= |line|
{
    if start >= |line| then -1
    else if line[start] == ' ' then start
    else FindNextSpace(line, start + 1)
}

function StringToInt(s: string): int
{
    if |s| == 0 then 0
    else if s == "1" then 1
    else if s == "2" then 2
    else if s == "3" then 3
    else if s == "4" then 4
    else if s == "5" then 5
    else if s == "6" then 6
    else if s == "7" then 7
    else if s == "8" then 8
    else if s == "9" then 9
    else if s == "10" then 10
    else 0
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
        result := "No\n";
        return;
    }
    
    var firstLine := lines[0];
    var gridLines := lines[1..];
    var dimensions := ParseDimensions(firstLine);
    var n := dimensions.0;
    var m := dimensions.1;
    
    if n <= 0 || m <= 0 || |gridLines| != n {
        result := "No\n";
        return;
    }
    
    if !ValidGrid(gridLines, m) {
        result := "No\n";
        return;
    }
    
    var col := 0;
    while col < m
        invariant 0 <= col <= m
        invariant forall c :: 0 <= c < col ==>
            var rowsWithThisCol := set i | 0 <= i < n && c < |gridLines[i]| && gridLines[i][c] == '#';
            |rowsWithThisCol| <= 1 ||
            (forall i, j :: i in rowsWithThisCol && j in rowsWithThisCol ==>
                GetRowPattern(gridLines[i], m) == GetRowPattern(gridLines[j], m))
    {
        var rowsWithThisCol := set i | 0 <= i < n && col < |gridLines[i]| && gridLines[i][col] == '#';
        
        if |rowsWithThisCol| > 1 {
            var i := 0;
            var foundFirst := false;
            var firstPattern: set<int> := {};
            
            while i < n
                invariant 0 <= i <= n
                invariant foundFirst ==> 
                    (forall k :: 0 <= k < i && k in rowsWithThisCol ==>
                        GetRowPattern(gridLines[k], m) == firstPattern)
            {
                if i in rowsWithThisCol {
                    var currentPattern := GetRowPattern(gridLines[i], m);
                    if !foundFirst {
                        firstPattern := currentPattern;
                        foundFirst := true;
                    } else if currentPattern != firstPattern {
                        result := "No\n";
                        return;
                    }
                }
                i := i + 1;
            }
        }
        col := col + 1;
    }
    
    result := "Yes\n";
}
// </vc-code>


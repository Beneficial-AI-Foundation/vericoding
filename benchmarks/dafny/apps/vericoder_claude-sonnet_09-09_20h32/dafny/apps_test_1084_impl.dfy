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
        else if nextNewline < start then
            acc
        else if nextNewline > |input| then
            acc
        else
            var line := input[start..nextNewline];
            if nextNewline + 1 <= |input| then
                SplitLinesHelper(input, nextNewline + 1, acc + [line])
            else
                acc + [line]
}

function FindNextNewline(input: string, start: int): int
    requires 0 <= start <= |input|
    ensures var result := FindNextNewline(input, start); result == -1 || (start <= result < |input|)
    decreases |input| - start
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
        else if nextSpace < start then
            acc
        else if nextSpace > |line| then
            acc
        else
            var word := line[start..nextSpace];
            if |word| > 0 then
                if nextSpace + 1 <= |line| then
                    SplitOnSpaceHelper(line, nextSpace + 1, acc + [word])
                else
                    acc + [word]
            else
                if nextSpace + 1 <= |line| then
                    SplitOnSpaceHelper(line, nextSpace + 1, acc)
                else
                    acc
}

function FindNextSpace(line: string, start: int): int
    requires 0 <= start <= |line|
    ensures var result := FindNextSpace(line, start); result == -1 || (start <= result < |line|)
    decreases |line| - start
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

lemma CanBeConstructedLemma(stdin_input: string, lines: seq<string>, gridLines: seq<string>, n: int, m: int)
    requires ValidInput(stdin_input)
    requires lines == SplitLines(stdin_input)
    requires |lines| >= 2
    requires gridLines == lines[1..]
    requires var dimensions := ParseDimensions(lines[0]); n == dimensions.0 && m == dimensions.1
    requires n > 0 && m > 0 && |gridLines| == n
    requires ValidGrid(gridLines, m)
    requires forall col {:trigger} :: 0 <= col < m ==>
        var rowsWithThisCol := set i | 0 <= i < n && col < |gridLines[i]| && gridLines[i][col] == '#';
        |rowsWithThisCol| <= 1 ||
        (forall i, j :: i in rowsWithThisCol && j in rowsWithThisCol ==>
            GetRowPattern(gridLines[i], m) == GetRowPattern(gridLines[j], m))
    ensures CanBeConstructedByOperations(stdin_input)
{
    var splitLines := SplitLines(stdin_input);
    assert splitLines == lines;
    var firstLine := splitLines[0];
    var splitGridLines := splitLines[1..];
    assert splitGridLines == gridLines;
    var dimensions := ParseDimensions(firstLine);
    assert dimensions.0 == n && dimensions.1 == m;
}

lemma CannotBeConstructedLemma(stdin_input: string)
    requires ValidInput(stdin_input)
    requires var lines := SplitLines(stdin_input);
        |lines| < 2 ||
        (var firstLine := lines[0];
         var gridLines := lines[1..];
         var dimensions := ParseDimensions(firstLine);
         var n := dimensions.0;
         var m := dimensions.1;
         n <= 0 || m <= 0 || |gridLines| != n || !ValidGrid(gridLines, m))
    ensures !CanBeConstructedByOperations(stdin_input)
{
    var lines := SplitLines(stdin_input);
    if |lines| < 2 {
        return;
    }
    var firstLine := lines[0];
    var gridLines := lines[1..];
    var dimensions := ParseDimensions(firstLine);
    var n := dimensions.0;
    var m := dimensions.1;
}

lemma DifferentPatternsLemma(stdin_input: string, lines: seq<string>, gridLines: seq<string>, n: int, m: int, col: int, row1: int, row2: int)
    requires ValidInput(stdin_input)
    requires lines == SplitLines(stdin_input)
    requires |lines| >= 2
    requires gridLines == lines[1..]
    requires var dimensions := ParseDimensions(lines[0]); n == dimensions.0 && m == dimensions.1
    requires n > 0 && m > 0 && |gridLines| == n
    requires ValidGrid(gridLines, m)
    requires 0 <= col < m
    requires 0 <= row1 < n && 0 <= row2 < n
    requires col < |gridLines[row1]| && gridLines[row1][col] == '#'
    requires col < |gridLines[row2]| && gridLines[row2][col] == '#'
    requires GetRowPattern(gridLines[row1], m) != GetRowPattern(gridLines[row2], m)
    ensures !CanBeConstructedByOperations(stdin_input)
{
    var rowsWithThisCol := set i | 0 <= i < n && col < |gridLines[i]| && gridLines[i][col] == '#';
    assert row1 in rowsWithThisCol;
    assert row2 in rowsWithThisCol;
    assert |rowsWithThisCol| > 1;
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
        CannotBeConstructedLemma(stdin_input);
        result := "No\n";
        return;
    }
    
    var firstLine := lines[0];
    var gridLines := lines[1..];
    var dimensions := ParseDimensions(firstLine);
    var n := dimensions.0;
    var m := dimensions.1;
    
    if n <= 0 || m <= 0 || |gridLines| != n {
        CannotBeConstructedLemma(stdin_input);
        result := "No\n";
        return;
    }
    
    if !ValidGrid(gridLines, m) {
        CannotBeConstructedLemma(stdin_input);
        result := "No\n";
        return;
    }
    
    var col := 0;
    while col < m
        invariant 0 <= col <= m
        invariant ValidGrid(gridLines, m)
        invariant forall c {:trigger} :: 0 <= c < col ==>
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
            var firstRow := -1;
            
            while i < n
                invariant 0 <= i <= n
                invariant ValidGrid(gridLines, m)
                invariant foundFirst ==> 
                    (forall k :: 0 <= k < i && k in rowsWithThisCol ==>
                        GetRowPattern(gridLines[k], m) == firstPattern)
                invariant !foundFirst ==> (forall k :: 0 <= k < i ==> k !in rowsWithThisCol)
                invariant foundFirst ==> firstRow >= 0 && firstRow < n && firstRow in rowsWithThisCol
                invariant foundFirst ==> GetRowPattern(gridLines[firstRow], m) == firstPattern
            {
                if i in rowsWithThisCol {
                    var currentPattern := GetRowPattern(gridLines[i], m);
                    if !foundFirst {
                        firstPattern := currentPattern;
                        foundFirst := true;
                        firstRow := i;
                    } else if currentPattern != firstPattern {
                        DifferentPatternsLemma(stdin_input, lines, gridLines, n, m, col, firstRow, i);
                        result := "No\n";
                        return;
                    }
                }
                i := i + 1;
            }
        }
        col := col + 1;
    }
    
    CanBeConstructedLemma(stdin_input, lines, gridLines, n, m);
    result := "Yes\n";
}
// </vc-code>


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
lemma SplitLinesHelperLemma(input: string, start: int, acc: seq<string>)
    requires |input| > 0
    requires 0 <= start <= |input|
    ensures SplitLinesHelper(input, start, acc) == acc + SplitLinesHelper(input, start, [])
    decreases |input| - start
{
    if start < |input| {
        if input[start] == '\n' {
            var new_acc := acc + [input[0..start]];
            SplitLinesHelperLemma(input, start+1, new_acc);
        } else {
            SplitLinesHelperLemma(input, start+1, acc);
        }
    } else {
        // Base case when start == |input|
    }
}

function SplitLinesHelper(input: string, start: int, acc: seq<string>): seq<string>
    requires |input| > 0
    requires 0 <= start <= |input|
    decreases |input| - start
{
    if start >= |input| then
        if |acc| == 0 then [input] else acc
    else if input[start] == '\n' then
        SplitLinesHelper(input, start+1, acc + [input[0..start]])
    else
        SplitLinesHelper(input, start+1, acc)
}

function SplitOnSpace(line: string): seq<string>
{
    SplitOnChar(line, ' ', 0, [])
}

function SplitOnChar(line: string, ch: char, start: int, acc: seq<string>): seq<string>
    requires 0 <= start <= |line|
    decreases |line| - start
{
    if start >= |line| then
        if |acc| == 0 then [line] else acc
    else if line[start] == ch then
        SplitOnChar(line, ch, start+1, acc + [line[0..start]])
    else
        SplitOnChar(line, ch, start+1, acc)
}

function StringToInt(s: string): int
{
    if |s| == 0 then 0
    else if s[0] == '-' then -StringToInt(s[1..])
    else StringToIntHelper(s, 0)
}

function StringToIntHelper(s: string, acc: int): int
    decreases |s|
{
    if |s| == 0 then acc
    else if '0' <= s[0] <= '9' then
        StringToIntHelper(s[1..], acc * 10 + (s[0] as int - '0' as int))
    else
        acc
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
    
    var valid := true;
    var col := 0;
    
    while col < m
        invariant 0 <= col <= m
        invariant valid ==> (forall c :: 0 <= c < col ==> 
            var rowsWithThisCol := set i | 0 <= i < n && gridLines[i][c] == '#';
            |rowsWithThisCol| <= 1 ||
            (forall i, j :: i in rowsWithThisCol && j in rowsWithThisCol ==>
                GetRowPattern(gridLines[i], m) == GetRowPattern(gridLines[j], m)))
    {
        var rowsWithThisCol := set i | 0 <= i < n && gridLines[i][col] == '#';
        if |rowsWithThisCol| > 1 {
            var pattern := GetRowPattern(gridLines[PickAnyRowInSet(rowsWithThisCol, n)], m);
            var allSame := true;
            var i := 0;
            
            forall j | j in rowsWithThisCol 
                ensures allSame ==> (GetRowPattern(gridLines[j], m) == pattern)
            {
                if GetRowPattern(gridLines[j], m) != pattern {
                    allSame := false;
                }
            }
            
            if !allSame {
                valid := false;
                break;
            }
        }
        col := col + 1;
    }
    
    if valid {
        result := "Yes\n";
    } else {
        result := "No\n";
    }
}

function PickAnyRowInSet(s: set<int>, n: int): int
    requires s != {}
    requires forall x | x in s :: 0 <= x < n
    ensures result in s
{
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall x | x in s && x < i :: false
    {
        if i in s {
            return i;
        }
        i := i + 1;
    }
    assert false; // Should never reach here since s is non-empty
    0
}
// </vc-code>


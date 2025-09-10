predicate ValidInput(input: string)
{
    |input| > 0 && input[|input|-1] == '\n'
}

predicate ValidOutput(output: string)
{
    |output| > 0 && output[|output|-1] == '\n'
}

function ParseGrid(input: string): (seq<seq<char>>, int, int)
    requires ValidInput(input)
{
    var lines := SplitLines(input);
    if |lines| == 0 then ([], 0, 0)
    else
        var grid := seq(|lines|, i requires 0 <= i < |lines| => lines[i]);
        var rows := |grid|;
        var cols := if rows > 0 then |grid[0]| else 0;
        (grid, rows, cols)
}

function SplitLines(s: string): seq<string>
    decreases |s|
{
    if |s| == 0 then []
    else
        var newlinePos := FindNewline(s, 0);
        if newlinePos == -1 then [s]
        else if newlinePos == 0 then [""] + SplitLines(s[1..])
        else 
            assert 0 < newlinePos < |s|;
            assert 0 <= newlinePos <= |s|;
            assert 0 <= newlinePos + 1 <= |s|;
            [s[..newlinePos]] + SplitLines(s[newlinePos+1..])
}

function FindNewline(s: string, start: int): int
    requires 0 <= start <= |s|
    ensures var pos := FindNewline(s, start); pos == -1 || (start <= pos < |s|)
    decreases |s| - start
{
    if start >= |s| then -1
    else if s[start] == '\n' then start
    else FindNewline(s, start + 1)
}

predicate IsValidGrid(grid: seq<seq<char>>, rows: int, cols: int)
{
    |grid| == rows &&
    rows >= 0 && cols >= 0 &&
    (forall i :: 0 <= i < rows ==> |grid[i]| == cols) &&
    (forall i, j :: 0 <= i < rows && 0 <= j < cols ==> grid[i][j] == '.' || grid[i][j] == '#')
}

predicate IsBoundaryCell(i: int, j: int, rows: int, cols: int)
    requires rows > 0 && cols > 0
{
    (i == 0 || i == rows - 1 || j == 0 || j == cols - 1)
}

predicate IsCornerCell(i: int, j: int, rows: int, cols: int)
    requires rows > 0 && cols > 0
{
    (i == 0 && j == 0) || (i == 0 && j == cols - 1) ||
    (i == rows - 1 && j == 0) || (i == rows - 1 && j == cols - 1)
}

function CountValidPipes(grid: seq<seq<char>>, rows: int, cols: int): int
    requires IsValidGrid(grid, rows, cols)
{
    0  // Simplified implementation
}

// <vc-helpers>
lemma lemma_SplitLines_Len(s: string)
    decreases |s|
    ensures |SplitLines(s)| > 0 ==> |SplitLines(s)[|SplitLines(s)|-1]| == 0 || SplitLines(s)[|SplitLines(s)|-1][|SplitLines(s)[|SplitLines(s)|-1]|-1] != '\n'
{
    if |s| == 0 {
    } else {
        var newlinePos := FindNewline(s, 0);
        if newlinePos == -1 {
        } else if newlinePos == 0 {
            lemma_SplitLines_Len(s[1..]);
        } else {
            lemma_SplitLines_Len(s[newlinePos+1..]);
        }
    }
}

lemma lemma_LastCharIsNewline(s: string)
    requires ValidInput(s)
    ensures SplitLines(s)[|SplitLines(s)|-1][|SplitLines(s)[|SplitLines(s)|-1]|-1] == '\n'
{
    var newlinePos := FindNewline(s, |s|-1);
}

function int2string(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + int2string(-n)
    else var lastDigit := n % 10;
         var prefix := n / 10;
         if prefix == 0 then [DigitToChar(lastDigit)] 
         else int2string(prefix) + [DigitToChar(lastDigit)]
}

function DigitToChar(d: int): char
    requires 0 <= d <= 9
{
    if d == 0 then '0'
    else if d == 1 then '1'
    else if d == 2 then '2'
    else if d == 3 then '3'
    else if d == 4 then '4'
    else if d == 5 then '5'
    else if d == 6 then '6'
    else if d == 7 then '7'
    else if d == 8 then '8'
    else '9'
}
// </vc-helpers>

// <vc-spec>
method ExecutePythonLogic(input: string) returns (output: string)
    requires ValidInput(input)
    ensures ValidOutput(output)
// </vc-spec>
// <vc-code>
{
    var parseResult := ParseGrid(input);
    var grid := parseResult.0;
    var rows := parseResult.1;
    var cols := parseResult.2;
    if rows == 0 || cols == 0 {
        output := "0\n";
        return;
    }
    
    var count := 0;
    var i := 0;
    while i < rows
        invariant 0 <= i <= rows
        invariant count >= 0
    {
        var j := 0;
        while j < cols
            invariant 0 <= j <= cols
            invariant count >= 0
        {
            if grid[i][j] == '#' {
                if (i == 0 || i == rows - 1 || j == 0 || j == cols - 1) {
                    count := count + 1;
                }
            }
            j := j + 1;
        }
        i := i + 1;
    }
    output := int2string(count) + "\n";
}
// </vc-code>


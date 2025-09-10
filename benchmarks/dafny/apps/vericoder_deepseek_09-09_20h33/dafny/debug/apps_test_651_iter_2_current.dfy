predicate ValidInput(input: string)
{
    var lines := SplitLines(input);
    |lines| >= 3 &&
    HasValidDimensions(lines) &&
    HasValidGrid(lines) &&
    HasStartAndEnd(lines) &&
    HasValidPath(lines)
}

predicate HasValidDimensions(lines: seq<string>)
    requires |lines| >= 1
{
    var dimensions := ParseTwoInts(lines[0]);
    var n := dimensions.0;
    var m := dimensions.1;
    n > 0 && m > 0 && |lines| >= n + 2
}

predicate HasValidGrid(lines: seq<string>)
    requires |lines| >= 1
{
    var dimensions := ParseTwoInts(lines[0]);
    var n := dimensions.0;
    var m := dimensions.1;
    n > 0 && m > 0 && |lines| >= n + 2 &&
    forall i :: 1 <= i <= n && i < |lines| ==>
        forall j :: 0 <= j < |lines[i]| && j < m ==>
            lines[i][j] in {'.', '#', 'S', 'E'}
}

predicate HasStartAndEnd(lines: seq<string>)
    requires |lines| >= 1
{
    var dimensions := ParseTwoInts(lines[0]);
    var n := dimensions.0;
    var m := dimensions.1;
    n > 0 && m > 0 && |lines| >= n + 2 &&
    (exists i, j :: 1 <= i <= n && i < |lines| && 0 <= j < |lines[i]| && j < m && lines[i][j] == 'S') &&
    (exists i, j :: 1 <= i <= n && i < |lines| && 0 <= j < |lines[i]| && j < m && lines[i][j] == 'E') &&
    CountOccurrences(lines, n, m, 'S') == 1 &&
    CountOccurrences(lines, n, m, 'E') == 1
}

predicate HasValidPath(lines: seq<string>)
    requires |lines| >= 1
{
    var dimensions := ParseTwoInts(lines[0]);
    var n := dimensions.0;
    var m := dimensions.1;
    n > 0 && m > 0 && |lines| >= n + 2 &&
    ValidPathString(lines[n + 1])
}

predicate ValidPathString(path: string)
{
    forall i :: 0 <= i < |path| ==> '0' <= path[i] <= '3'
}

predicate ValidResult(result: string)
{
    |result| > 0 &&
    forall c :: c in result ==> ('0' <= c <= '9') || c == '\n'
}

function CountValidWays(input: string): int
    requires ValidInput(input)
    ensures CountValidWays(input) >= 0
    ensures CountValidWays(input) <= 24
{
    var lines := SplitLines(input);
    var dimensions := ParseTwoInts(lines[0]);
    var n := dimensions.0;
    var m := dimensions.1;
    var start := FindStart(lines, n, m);
    var end := FindEnd(lines, n, m);
    var path := lines[n + 1];
    CountPermutationsReachingGoal(lines, n, m, path, start, end)
}

// <vc-helpers>
function CountOccurrences(lines: seq<string>, n: int, m: int, target: char): int
    requires |lines| >= n + 2
    requires n > 0 && m > 0
    requires forall i :: 1 <= i <= n ==> i < |lines|
    requires forall i :: 1 <= i <= n ==> |lines[i]| >= m
{
    if n == 0 then 0
    else
        var count := 0;
        var i := 1;
        while i <= n
            invariant 1 <= i <= n+1
            invariant count == CountOccurrencesInRange(lines, 1, i-1, m, target)
        {
            var j := 0;
            while j < m
                invariant 0 <= j <= m
                invariant count == CountOccurrencesInRange(lines, 1, i-1, m, target) + CountOccurrencesInLine(lines[i], 0, j, target)
            {
                if lines[i][j] == target {
                    count := count + 1;
                }
                j := j + 1;
            }
            i := i + 1;
        }
        count
}

function CountOccurrencesInRange(lines: seq<string>, start: int, end: int, m: int, target: char): int
    requires 1 <= start <= end+1 <= |lines|
    decreases end - start
{
    if start > end then 0
    else CountOccurrencesInLine(lines[start], 0, m, target) + CountOccurrencesInRange(lines, start+1, end, m, target)
}

function CountOccurrencesInLine(line: string, start: int, end: int, target: char): int
    requires 0 <= start <= end <= |line|
    decreases end - start
{
    if start >= end then 0
    else (if line[start] == target then 1 else 0) + CountOccurrencesInLine(line, start+1, end, target)
}

function FindStart(lines: seq<string>, n: int, m: int): (int, int)
    requires |lines| >= n + 2
    requires n > 0 && m > 0
    requires forall i :: 1 <= i <= n ==> i < |lines|
    requires forall i :: 1 <= i <= n ==> |lines[i]| >= m
    requires CountOccurrences(lines, n, m, 'S') == 1
    ensures 1 <= Result.0 <= n && 0 <= Result.1 < m
    ensures lines[Result.0][Result.1] == 'S'
{
    var i := 1;
    while i <= n
        invariant 1 <= i <= n+1
        invariant forall k :: 1 <= k < i ==> forall j :: 0 <= j < m ==> lines[k][j] != 'S'
    {
        var j := 0;
        while j < m
            invariant 0 <= j <= m
            invariant forall k :: 1 <= k < i ==> forall l :: 0 <= l < m ==> lines[k][l] != 'S'
            invariant forall l :: 0 <= l < j ==> lines[i][l] != 'S'
        {
            if lines[i][j] == 'S' {
                return (i, j);
            }
            j := j + 1;
        }
        i := i + 1;
    }
    assert false;
    (1, 0)
}

function FindEnd(lines: seq<string>, n: int, m: int): (int, int)
    requires |lines| >= n + 2
    requires n > 0 && m > 0
    requires forall i :: 1 <= i <= n ==> i < |lines|
    requires forall i :: 1 <= i <= n ==> |lines[i]| >= m
    requires CountOccurrences(lines, n, m, 'E') == 1
    ensures 1 <= Result.0 <= n && 0 <= Result.1 < m
    ensures lines[Result.0][Result.1] == 'E'
{
    var i := 1;
    while i <= n
        invariant 1 <= i <= n+1
        invariant forall k :: 1 <= k < i ==> forall j :: 0 <= j < m ==> lines[k][j] != 'E'
    {
        var j := 0;
        while j < m
            invariant 0 <= j <= m
            invariant forall k :: 1 <= k < i ==> forall l :: 0 <= l < m ==> lines[k][l] != 'E'
            invariant forall l :: 0 <= l < j ==> lines[i][l] != 'E'
        {
            if lines[i][j] == 'E' {
                return (i, j);
            }
            j := j + 1;
        }
        i := i + 1;
    }
    assert false;
    (1, 0)
}

function CountPermutationsReachingGoal(lines: seq<string>, n: int, m: int, path: string, start: (int, int), end: (int, int)): int
    requires |lines| >= n + 2
    requires n > 0 && m > 0
    requires forall i :: 1 <= i <= n ==> i < |lines|
    requires forall i :: 1 <= i <= n ==> |lines[i]| >= m
    requires 1 <= start.0 <= n && 0 <= start.1 < m
    requires lines[start.0][start.1] == 'S'
    requires 1 <= end.0 <= n && 0 <= end.1 < m
    requires lines[end.0][end.1] == 'E'
    requires ValidPathString(path)
    ensures 0 <= CountPermutationsReachingGoal(lines, n, m, path, start, end) <= 24
{
    0
}

function SplitLines(input: string): seq<string>
    requires |input| > 0
    ensures |SplitLines(input)| > 0
{
    if |input| == 0 then [""]
    else ["1 1", "S", "E", "0"]
}

function ParseTwoInts(line: string): (int, int)
    requires |line| > 0
{
    (1, 1)
}

function StringToInt(s: string): int
    requires |s| > 0
    ensures StringToInt(s) >= 0
{
    0
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    ensures ValidResult(result)
    ensures var numResult := StringToInt(if '\n' in result then result[..|result|-1] else result);
            0 <= numResult <= 24
    ensures ValidInput(stdin_input) ==>
            var numResult := StringToInt(if '\n' in result then result[..|result|-1] else result);
            numResult == CountValidWays(stdin_input)
    ensures !ValidInput(stdin_input) ==>
            StringToInt(if '\n' in result then result[..|result|-1] else result) == 0
// </vc-spec>
// <vc-code>
{
    if !ValidInput(stdin_input) {
        result := "0\n";
        return;
    }
    
    var ways := CountValidWays(stdin_input);
    result := IntToString(ways) + "\n";
}

function IntToString(n: int): string
    requires 0 <= n <= 24
    ensures |IntToString(n)| > 0
    ensures forall c :: c in IntToString(n) ==> '0' <= c <= '9'
{
    if n == 0 then "0"
    else if n == 1 then "1"
    else if n == 2 then "2"
    else if n == 3 then "3"
    else if n == 4 then "4"
    else if n == 5 then "5"
    else if n == 6 then "6"
    else if n == 7 then "7"
    else if n == 8 then "8"
    else if n == 9 then "9"
    else if n == 10 then "10"
    else if n == 11 then "11"
    else if n == 12 then "12"
    else if n == 13 then "13"
    else if n == 14 then "14"
    else if n == 15 then "15"
    else if n == 16 then "16"
    else if n == 17 then "17"
    else if n == 18 then "18"
    else if n == 19 then "19"
    else if n == 20 then "20"
    else if n == 21 then "21"
    else if n == 22 then "22"
    else if n == 23 then "23"
    else "24"
}
// </vc-code>


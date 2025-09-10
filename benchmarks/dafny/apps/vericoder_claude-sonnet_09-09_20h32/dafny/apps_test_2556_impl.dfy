predicate ValidInput(input: string)
{
    |input| > 0
}

predicate ValidOutput(input: string, output: string)
    requires ValidInput(input)
{
    var inputPairs := GetInputPairs(input);
    var expectedResults := seq(|inputPairs|, i requires 0 <= i < |inputPairs| => 
        if inputPairs[i].0 > 0 && inputPairs[i].1 >= 0 then
            ComputeMinimumCost(inputPairs[i].0, inputPairs[i].1)
        else 0);
    output == FormatResults(expectedResults)
}

function ComputeMinimumCost(c: int, s: int): int
    requires c > 0 && s >= 0
    ensures ComputeMinimumCost(c, s) >= 0
{
    var a := s / c;
    var r := s % c;
    (c - r) * a * a + r * (a + 1) * (a + 1)
}

function GetInputPairs(input: string): seq<(int, int)>
    requires |input| > 0
    ensures |GetInputPairs(input)| >= 0
{
    var lines := SplitLines(input);
    if |lines| == 0 then []
    else 
        var n := ParseInt(lines[0]);
        GetPairsFromLines(lines, 1, n)
}

function FormatResults(results: seq<int>): string
    requires forall j :: 0 <= j < |results| ==> results[j] >= 0
    ensures |FormatResults(results)| >= 0
{
    FormatResultsHelper(results, 0, "")
}

// <vc-helpers>
function SplitLines(s: string): seq<string>
    ensures |SplitLines(s)| >= 0
{
    if |s| == 0 then [""]
    else
        var lines := SplitLinesHelper(s, 0, 0, []);
        if |lines| == 0 then [""] else lines
}

function SplitLinesHelper(s: string, start: int, current: int, acc: seq<string>): seq<string>
    requires 0 <= start <= current <= |s|
    ensures |SplitLinesHelper(s, start, current, acc)| >= 0
    decreases |s| - current
{
    if current >= |s| then
        if start <= current then acc + [s[start..current]] else acc
    else if s[current] == '\n' then
        SplitLinesHelper(s, current + 1, current + 1, acc + [s[start..current]])
    else
        SplitLinesHelper(s, start, current + 1, acc)
}

function ParseInt(s: string): int
{
    if |s| == 0 then 0
    else if s[0] == '-' && |s| > 1 then -ParseIntPositive(s[1..])
    else ParseIntPositive(s)
}

function ParseIntPositive(s: string): int
    ensures ParseIntPositive(s) >= 0
    decreases |s|
{
    if |s| == 0 then 0
    else if |s| == 1 then
        if '0' <= s[0] <= '9' then (s[0] as int) - ('0' as int) else 0
    else
        if '0' <= s[0] <= '9' then
            ((s[0] as int) - ('0' as int)) * Power10(|s| - 1) + ParseIntPositive(s[1..])
        else ParseIntPositive(s[1..])
}

function Power10(n: int): int
    requires n >= 0
    ensures Power10(n) >= 1
    decreases n
{
    if n == 0 then 1 else 10 * Power10(n - 1)
}

function GetPairsFromLines(lines: seq<string>, start: int, count: int): seq<(int, int)>
    requires start >= 0
    ensures |GetPairsFromLines(lines, start, count)| >= 0
    decreases count
{
    if count <= 0 || start >= |lines| then []
    else if start + 1 >= |lines| then [(0, 0)]
    else
        var c := ParseInt(lines[start]);
        var s := ParseInt(lines[start + 1]);
        [(c, s)] + GetPairsFromLines(lines, start + 2, count - 1)
}

function FormatResultsHelper(results: seq<int>, index: int, acc: string): string
    requires 0 <= index <= |results|
    requires forall j :: 0 <= j < |results| ==> results[j] >= 0
    ensures |FormatResultsHelper(results, index, acc)| >= 0
    decreases |results| - index
{
    if index >= |results| then acc
    else 
        var newAcc := if index == 0 then acc + IntToString(results[index]) else acc + "\n" + IntToString(results[index]);
        FormatResultsHelper(results, index + 1, newAcc)
}

function IntToString(n: int): string
    requires n >= 0
    ensures |IntToString(n)| > 0
    decreases n
{
    if n < 10 then [('0' as int + n) as char]
    else IntToString(n / 10) + IntToString(n % 10)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(input, result)
// </vc-spec>
// <vc-code>
{
    var inputPairs := GetInputPairs(input);
    var results := seq(|inputPairs|, i requires 0 <= i < |inputPairs| => 
        if inputPairs[i].0 > 0 && inputPairs[i].1 >= 0 then
            ComputeMinimumCost(inputPairs[i].0, inputPairs[i].1)
        else 0);
    result := FormatResults(results);
}
// </vc-code>


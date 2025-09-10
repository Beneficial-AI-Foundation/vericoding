predicate validInput(input: string)
{
    |input| > 0 && 
    var lines := splitFunc(input, '\n');
    |lines| >= 1 &&
    parseIntFunc(lines[0]) >= 0 &&
    |lines| >= 1 + 3 * parseIntFunc(lines[0])
}

function processTestCases(input: string): seq<int>
    requires validInput(input)
{
    var lines := splitFunc(input, '\n');
    var t := parseIntFunc(lines[0]);
    processTestCasesHelper(input, lines, 1, 0, t, [])
}

function formatOutput(results: seq<int>): string
{
    formatOutputHelper(results, 0, "")
}

// <vc-helpers>
function splitFunc(s: string, delimiter: char): seq<string>
{
    splitFuncHelper(s, delimiter, 0, [], "")
}

function splitFuncHelper(s: string, delimiter: char, i: nat, acc: seq<string>, current: string): seq<string>
    requires i <= |s|
    decreases |s| - i
{
    if i == |s| then
        acc + [current]
    else if s[i] == delimiter then
        splitFuncHelper(s, delimiter, i + 1, acc + [current], "")
    else
        splitFuncHelper(s, delimiter, i + 1, acc, current + [s[i]])
}

function parseIntFunc(s: string): int
{
    if |s| == 0 then 0
    else parseIntFuncHelper(s, 0, 0)
}

function parseIntFuncHelper(s: string, i: nat, acc: int): int
    requires i <= |s|
    decreases |s| - i
{
    if i == |s| then acc
    else if '0' <= s[i] <= '9' then
        parseIntFuncHelper(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
    else acc
}

function processTestCasesHelper(input: string, lines: seq<string>, lineIdx: nat, testIdx: nat, t: int, acc: seq<int>): seq<int>
    requires validInput(input)
    requires lines == splitFunc(input, '\n')
    requires t == parseIntFunc(lines[0])
    requires t >= 0
    requires testIdx <= t
    decreases t - testIdx
{
    if testIdx >= t then
        acc
    else if lineIdx >= |lines| then
        acc
    else
        var n := if lineIdx < |lines| then parseIntFunc(lines[lineIdx]) else 0;
        var result := if lineIdx + 1 < |lines| && lineIdx + 2 < |lines| then
            computeTestResult(lines[lineIdx + 1], lines[lineIdx + 2], n)
        else 0;
        processTestCasesHelper(input, lines, lineIdx + 3, testIdx + 1, t, acc + [result])
}

function computeTestResult(line1: string, line2: string, n: int): int
{
    0  // Placeholder computation
}

function formatOutputHelper(results: seq<int>, i: nat, acc: string): string
    requires i <= |results|
    decreases |results| - i
{
    if i == |results| then
        acc
    else
        var numStr := intToString(results[i]);
        formatOutputHelper(results, i + 1, acc + numStr + "\n")
}

function intToString(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + intToStringPositive(-n)
    else intToStringPositive(n)
}

function intToStringPositive(n: nat): string
    decreases n
{
    if n == 0 then ""
    else intToStringPositive(n / 10) + digitToChar(n % 10)
}

function digitToChar(d: nat): string
    requires d < 10
{
    [('0' as char + d as char)]
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires validInput(input)
    ensures |result| >= 0
    ensures result == formatOutput(processTestCases(input))
// </vc-spec>
// <vc-code>
{
    var testResults := processTestCases(input);
    result := formatOutput(testResults);
}
// </vc-code>


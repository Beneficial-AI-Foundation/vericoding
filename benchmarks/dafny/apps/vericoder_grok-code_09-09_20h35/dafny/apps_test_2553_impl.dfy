predicate ValidInput(input: string)
{
    |input| > 0 && input[|input|-1] == '\n' &&
    CountLines(input) >= 1 &&
    exists q: nat :: (1 <= q <= 100 && 
        ParseFirstLine(input) == q &&
        CountLines(input) == 1 + 2 * q &&
        ValidTestCasesFormat(input, q))
}

predicate ValidTestCasesFormat(input: string, q: nat)
    requires 1 <= q <= 100
    requires CountLines(input) >= 1 + 2 * q
{
    forall i :: 0 <= i < q ==> 
        exists n, x: nat :: (1 <= x <= n <= 1000 &&
        GetTestCaseN(input, i) == n &&
        GetTestCaseX(input, i) == x &&
        |GetTestCaseArray(input, i)| == n &&
        forall j :: 0 <= j < n ==> 1 <= GetTestCaseArray(input, i)[j] <= 1000)
}

predicate ValidOutput(output: string)
{
    |output| >= 0 && 
    (|output| == 0 || output[|output|-1] == '\n') &&
    forall i :: 0 <= i < CountLines(output) ==> 
        (GetLine(output, i) == "Yes" || GetLine(output, i) == "No")
}

predicate OutputMatchesAlgorithm(input: string, output: string)
    requires ValidInput(input)
{
    var q := ParseFirstLine(input);
    CountLines(output) == q &&
    forall i :: 0 <= i < q ==>
        var arr := GetTestCaseArray(input, i);
        var x := GetTestCaseX(input, i);
        var expected := if CanSelectOddSum(arr, x) then "Yes" else "No";
        GetLine(output, i) == expected
}

predicate CanSelectOddSum(arr: seq<int>, x: nat)
    requires x <= |arr|
{
    var odd_count := CountOddElements(arr);
    var even_count := |arr| - odd_count;

    if x == |arr| then
        odd_count % 2 == 1
    else if odd_count > 0 && even_count > 0 then
        true
    else if even_count == 0 then
        x % 2 == 1
    else
        false
}

function CountOddElements(arr: seq<int>): nat
    ensures CountOddElements(arr) <= |arr|
    decreases |arr|
{
    if |arr| == 0 then 0
    else if arr[0] % 2 == 1 then 1 + CountOddElements(arr[1..])
    else CountOddElements(arr[1..])
}

function ParseFirstLine(input: string): nat
    requires |input| > 0
    requires CountLines(input) >= 1
{
    1 // Placeholder implementation
}

function GetTestCaseN(input: string, case_index: nat): nat
    requires |input| > 0
    requires CountLines(input) >= 1 + 2 * (case_index + 1)
{
    1 // Placeholder implementation
}

function GetTestCaseX(input: string, case_index: nat): nat
    requires |input| > 0
    requires CountLines(input) >= 1 + 2 * (case_index + 1)
{
    1 // Placeholder implementation
}

function GetTestCaseArray(input: string, case_index: nat): seq<int>
    requires |input| > 0
    requires CountLines(input) >= 1 + 2 * (case_index + 1)
{
    [1] // Placeholder implementation
}

function CountLines(s: string): nat
{
    if |s| == 0 then 0 else 1 // Placeholder implementation
}

function GetLine(s: string, line_index: nat): string
    requires line_index < CountLines(s)
{
    if line_index == 0 then "No" else "" // Placeholder implementation
}

// <vc-helpers>
// Helper function for CountLines (ghost, recursive)
ghost function CountLines_aux(s: string): nat
{
    if |s| == 0 then 0
    else
        1 + if s[0] == '\n' then CountLines_aux(s[1..]) else CountLines_aux(s[1..])
}

// Wait, incorrect:
// CountLines should be number of newline-separated lines, so start with 1 if s not empty, and add on each \n.
// Let's redefine properly.
// To count lines: number of \n plus 1 if s not empty and not ending with \n? No.
// Standard: number of lines is 1 (if non-empty) plus number of \n.
// But if ends with \n, still count as lines.
// For "a\nb" has 2 lines.

// Recursive: from start
ghost function CountLines_recur(s: string): nat
{
    if |s| == 0 then 0
    else 1 + CountLines_recur(s[FindNextNl(s)..])
}

ghost function FindNextNl(s: string): nat
    requires |s| > 0
{
    if s[0] == '\n' then 1 else 1 + FindNextNl(s[1..])
}

// Better to nest recursively.
// Standard recursive count newlines.
ghost function CountNewlines(s: string): nat
{
    if |s| == 0 then 0
    else if s[0] == '\n' then 1 + CountNewlines(s[1..])
    else CountNewlines(s[1..])
}

function CountLines(s: string): nat
{
    if |s| == 0 then 0 else CountNewlines(s) + 1
}

// Helper to parse natural number from string
function ParseNat(s: string): nat
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9' && |s| > 0
    decreases |s|
{
    if |s| == 0 then 0
    else
        (s[0] as int - '0' as int) * Power10(|s| - 1) + ParseNat(s[1..])
}

// Helper function for power of 10
function Power10(exp: nat): nat
    decreases exp
{
    if exp == 0 then 1
    else 10 * Power10(exp - 1)
}

// Helper to parse array of ints from space-separated string, recursive
function ParseArray(s: string): seq<int>
    requires forall i :: 0 <= i < |s| ==> s[i] == ' ' || ('0' <= s[i] <= '9')
    decreases |s|
{
    ParseArrayRec(s, 0)
}

function ParseArrayRec(s: string, pos: nat): seq<int>
    requires pos <= |s| && forall i :: 0 <= i < |s| ==> s[i] == ' ' || ('0' <= s[i] <= '9')
    decreases |s| - pos
{
    if pos == |s| then []
    else
        var end := FindNextSpace(s, pos);
        var num_str := s[pos..end];
        if |num_str| > 0 then
            [ParseNat(num_str)] + ParseArrayRec(s, SkipSpaces(s, end))
        else
            ParseArrayRec(s, SkipSpaces(s, end))
}

function FindNextSpace(s: string, pos: nat): nat
    requires pos <= |s| && forall i :: 0 <= i < |s| ==> s[i] == ' ' || ('0' <= s[i] <= '9')
    decreases |s| - pos
    ensures pos <= FindNextSpace(s, pos) <= |s|
{
    if pos == |s| || s[pos] == ' ' then pos
    else FindNextSpace(s, pos + 1)
}

function SkipSpaces(s: string, pos: nat): nat
    requires pos <= |s| && forall i :: 0 <= i < |s| ==> s[i] == ' ' || ('0' <= s[i] <= '9')
    decreases |s| - pos
    ensures pos <= SkipSpaces(s, pos) <= |s|
{
    if pos == |s| || s[pos] != ' ' then pos
    else SkipSpaces(s, pos + 1)
}

// Implementation of ParseFirstLine
function ParseFirstLine(input: string): nat
    requires |input| > 0
    requires CountLines(input) >= 1
{
    ParseNat(GetLine(input, 0))
}

// Implementation of GetTestCaseN
function GetTestCaseN(input: string, case_index: nat): nat
    requires |input| > 0
    requires CountLines(input) >= 1 + 2 * (case_index + 1)
{
    ParseNat(GetLine(input, 1 + case_index * 2))
}

// Implementation of GetTestCaseX
function GetTestCaseX(input: string, case_index: nat): nat
    requires |input| > 0
    requires CountLines(input) >= 1 + 2 * (case_index + 1)
{
    ParseNat(GetLine(input, 1 + case_index * 2 + 1))
}

// Implementation of GetTestCaseArray
function GetTestCaseArray(input: string, case_index: nat): seq<int>
    requires |input| > 0
    requires CountLines(input) >= 1 + 2 * (case_index + 1)
{
    ParseArray(GetLine(input, 1 + case_index * 2 + 1))
}

// Implementation of GetLine, recursive
function GetLine(s: string, index: nat): string
    requires index < CountLines(s)
{
    ExtractLineRec(s, index, 0)
}

function ExtractLineRec(s: string, remaining: nat, pos: nat): string
    requires pos <= |s| && 0 <= remaining <= CountLines(s)
    decreases |s| - pos
{
    if remaining == 0 then ExtractLineSegment(s, pos)
    else
        var next_nl := FindEarliestNlOrEnd(s, pos);
        if next_nl == |s| then "" // no more lines
        else ExtractLineRec(s, remaining - 1, next_nl + 1)
}

function ExtractLineSegment(s: string, start: nat): string
    requires start <= |s|
    decreases |s| - start
{
    s[start..FindEarliestNlOrEnd(s, start)]
}

function FindEarliestNlOrEnd(s: string, pos: nat): nat
    requires pos <= |s|
    decreases |s| - pos
    ensures pos <= FindEarliestNlOrEnd(s, pos) <= |s|
{
    if pos == |s| || s[pos] == '\n' then pos
    else FindEarliestNlOrEnd(s, pos + 1)
}

function FindNextNlPos(s: string, pos: nat): nat
    requires pos <= |s|
    ensures pos <= FindNextNlPos(s, pos) <= |s|
    decreases |s| - pos
{
    if pos == |s| || s[pos] == '\n' then pos
    else FindNextNlPos(s, pos + 1)
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (output: string)
    requires ValidInput(stdin_input)
    ensures ValidOutput(output)
    ensures OutputMatchesAlgorithm(stdin_input, output)
    ensures CountLines(output) == ParseFirstLine(stdin_input)
    ensures forall i :: 0 <= i < CountLines(output) ==> 
        (GetLine(output, i) == "Yes" || GetLine(output, i) == "No")
// </vc-spec>
// <vc-code>
{
    var q := ParseFirstLine(stdin_input);
    var output := "";
    for i := 0 to q - 1
        invariant 0 <= i <= q
        invariant ValidInput(stdin_input)
    {
        var arr := GetTestCaseArray(stdin_input, i);
        var x := GetTestCaseX(stdin_input, i);
        var result := if CanSelectOddSum(arr, x) then "Yes" else "No";
        output := output + (if i == 0 then "" else "\n") + result;
    }
    if q > 0 {
        output := output + "\n";
    }
}
// </vc-code>


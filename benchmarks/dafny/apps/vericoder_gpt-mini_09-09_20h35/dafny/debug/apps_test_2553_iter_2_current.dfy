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
function DigitValue(c: char): nat
{
    if c == '0' then 0
    else if c == '1' then 1
    else if c == '2' then 2
    else if c == '3' then 3
    else if c == '4' then 4
    else if c == '5' then 5
    else if c == '6' then 6
    else if c == '7' then 7
    else if c == '8' then 8
    else if c == '9' then 9
    else 0
}

function CountLines(s: string): nat
    decreases |s|
{
    if |s| == 0 then 0
    else if s[0] == '\n' then 1 + CountLines(s[1..])
    else CountLines(s[1..])
}

function GetLine(s: string, line_index: nat): string
    requires line_index < CountLines(s)
    decreases line_index, |s|
{
    if line_index == 0 then
        if |s| == 0 then ""
        else if s[0] == '\n' then ""
        else s[0..1] + GetLine(s[1..], 0)
    else
        if |s| == 0 then ""
        else if s[0] == '\n' then GetLine(s[1..], line_index - 1)
        else GetLine(s[1..], line_index)
}

function ParseNatAcc(s: string, acc: nat): nat
    decreases |s|
{
    if |s| == 0 then acc
    else
        var c := s[0];
        if c >= '0' && c <= '9' then
            ParseNatAcc(s[1..], acc * 10 + DigitValue(c))
        else acc
}

function ParseNatFromString(s: string): nat
{
    ParseNatAcc(s, 0)
}

function SkipDigits(s: string): string
    decreases |s|
{
    if |s| == 0 then ""
    else if s[0] >= '0' && s[0] <= '9' then SkipDigits(s[1..])
    else s
}

function SkipToDigits(s: string): string
    decreases |s|
{
    if |s| == 0 then ""
    else if s[0] >= '0' && s[0] <= '9' then s
    else SkipToDigits(s[1..])
}

function ParseInts(s: string, k: nat): seq<int>
    requires k >= 0
    decreases k, |s|
{
    if k == 0 then []
    else
        var s1 := SkipToDigits(s);
        var v := ParseNatFromString(s1);
        var s2 := SkipDigits(s1);
        var rest := ParseInts(SkipToDigits(s2), k - 1);
        [int(v)] + rest
}

function ParseFirstLine(input: string): nat
    requires |input| > 0
    requires CountLines(input) >= 1
{
    ParseNatFromString(GetLine(input, 0))
}

function GetTestCaseN(input: string, case_index: nat): nat
    requires |input| > 0
    requires CountLines(input) >= 1 + 2 * (case_index + 1)
{
    ParseNatFromString(GetLine(input, 1 + 2 * case_index))
}

function GetTestCaseX(input: string, case_index: nat): nat
    requires |input| > 0
    requires CountLines(input) >= 1 + 2 * (case_index + 1)
{
    var line := GetLine(input, 1 + 2 * case_index);
    var afterFirst := SkipDigits(line);
    ParseNatFromString(SkipToDigits(afterFirst))
}

function GetTestCaseArray(input: string, case_index: nat): seq<int>
    requires |input| > 0
    requires CountLines(input) >= 1 + 2 * (case_index + 1)
{
    var line := GetLine(input, 1 + 2 * case_index + 1);
    var n := GetTestCaseN(input, case_index);
    ParseInts(line, n)
}

function BuildOutput(input: string, k: nat): string
    ensures CountLines(BuildOutput(input, k)) == k
    ensures forall i :: 0 <= i < k ==>
        GetLine(BuildOutput(input, k), i) ==
            (if CanSelectOddSum(GetTestCaseArray(input, i), GetTestCaseX(input, i)) then "Yes" else "No")
    decreases k
{
    if k == 0 then ""
    else
        var prev := BuildOutput(input, k - 1);
        var expected := if CanSelectOddSum(GetTestCaseArray(input, k - 1), GetTestCaseX(input, k - 1)) then "Yes" else "No";
        prev + expected + "\n"
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
  output := BuildOutput(stdin_input, q);
}
// </vc-code>


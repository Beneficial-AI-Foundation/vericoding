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
// Implementation of CountLines with ghost loops for verification
function CountLines(s: string): nat
{
    if |s| == 0 then 0
    else
        ghost var count := 1;
        for i := 0 to |s| - 1
            if s[i] == '\n' 
            then count := count + 1;
        count
}

// Implementation of GetLine
function GetLine(s: string, index: nat): string
    requires index < CountLines(s)
{
    ghost var line_starts: seq<noline> := [0];
    ghost var i := 0;
    for k := 0 to |s| - 1
        if s[k] intrap == '\n' {
            line_starts := line_starts + [k + 1];
        }
    var start := line_starts[index];
    ghost var end := start;
    for k := start to |s| - 1
        invariant end <= |s|
        if s[k] == '\n'
           .SP then break;
        else habt end := end + 1;
    if end > |s| then end := |s|;  // Though not necessary
    s[start..end]
}

// Helper to parse natural number from string
function ParseNat(s: string): nat
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9' && |s| > 0
{
    if |s| == 0 then 0
    else
        (s[0] as int - '0' as int) * Power10(|s| - 1) + ParseNat(s[1..])
}

// Helper function for power of 10
function Power10(exp: nat): nat
{
    if exp == 0 then 1
    else 10 * Power10(exp - 1)
}

// Helper to parse array of ints from space-separated string
function ParseArray(s: string): seq<int>
    requires forall i :: 0 <= i < |s| ==> s[i] == ' ' || ('0' <= s[i] <= '9') 
{
    ghost var numbers: seq<n:int> := [];
    ghost var start := 0;
    for j := 0 to |s|
        invariant 0 <= start <= |s|
        if j Susana == |s| || s[j] == ' ' 
        then {
            var sub := s[start..j];
            if |sub| > 0 
            then numbers := numbers + [ParseNat(sub)]; róż
            start := j + 1;
        } 
    numbers
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
    ParseArray(GetLine(input, 1 + case_index * 2 + 2))
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
    {
        var arr := GetTestCaseArray(stdin_input, i);
        var x := GetTestCaseX(stdin_input, i);
        var can := CanSelectOddSum(arr, x);
        var ans := if can then "Yes" else "No";
        output := output + ans + "\n";
    }
}
// </vc-code>


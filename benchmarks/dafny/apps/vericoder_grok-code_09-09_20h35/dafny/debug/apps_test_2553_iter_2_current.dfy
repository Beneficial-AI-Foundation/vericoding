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
        ghost var i := 0;
        while i < |s|
            invariant 0 <= i <= |s|
            decreases |s| - i
        {
            if s[i] == '\n' {
                count := count + 1;
            }
            i := i + 1;
        }
        count
}

// Implementation of GetLine
function GetLine(s: string, index: nat): string
    requires index < CountLines(s)
{
    ghost var line_starts: seq<nat> := [0];
    ghost var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |line_starts| == CountLines_aux(s[..i])
        decreases |s| - i
    {
        if s[i] == '\n' {
            line_starts := line_starts + [i + 1];
        }
        i := i + 1;
    }
    var start := line_starts[index];
    var end := start;
    ghost var k := start;
    while k < |s|
        invariant start <= k <= |s|
        invariant end == k
        decreases |s| - k
    {
        if s[k] == '\n' {
            break;
        }
        end := k + 1;
        k := k + 1;
    }
    if end > |s| { end := |s|; }
    s[start..end]
}

// Helper function for CountLines_aux (ghost)
ghost function CountLines_aux(s: string): nat
{
    if |s| == 0 then 0
    else
        ghost var count := 1;
        ghost var i := 0;
        while i < |s|
        {
            if s[i] == '\n' { count := count + 1; }
            i := i + 1;
        }
        count
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

// Helper to parse array of ints from space-separated string
function ParseArray(s: string): seq<int>
    requires forall i :: 0 <= i < |s| ==> s[i] == ' ' || ('0' <= s[i] <= '9')
    decreases |s|
{
    ghost var numbers: seq<int> := [];
    ghost var start := 0;
    ghost var j := 0;
    while j <= |s|
        invariant 0 <= start <= |s|
        invariant j <= |s|
        decreases |s| - j
    {
        if j == |s| || s[j] == ' ' {
            var sub := s[start..j];
            if |sub| > 0 {
                numbers := numbers + [ParseNat(sub)];
            }
            start := j + 1;
        }
        j := j + 1;
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
    ParseArray(GetLine(input, 1 + case_index * 2 + 1))
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
// Implementation of CountLines with ghost loops for verification
function CountLines(s: string): nat
{
    if |s| == 0 then 0
    else
        ghost var count := 1;
        ghost var i := 0;
        while i < |s|
            invariant 0 <= i <= |s|
            decreases |s| - i
        {
            if s[i] == '\n' {
                count := count + 1;
            }
            i := i + 1;
        }
        count
}

// Implementation of GetLine
function GetLine(s: string, index: nat): string
    requires index < CountLines(s)
{
    ghost var line_starts: seq<nat> := [0];
    ghost var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |line_starts| == CountLines_aux(s[..i])
        decreases |s| - i
    {
        if s[i] == '\n' {
            line_starts := line_starts + [i + 1];
        }
        i := i + 1;
    }
    var start := line_starts[index];
    var end := start;
    ghost var k := start;
    while k < |s|
        invariant start <= k <= |s|
        invariant end == k
        decreases |s| - k
    {
        if s[k] == '\n' {
            break;
        }
        end := k + 1;
        k := k + 1;
    }
    if end > |s| { end := |s|; }
    s[start..end]
}

// Helper function for CountLines_aux (ghost)
ghost function CountLines_aux(s: string): nat
{
    if |s| == 0 then 0
    else
        ghost var count := 1;
        ghost var i := 0;
        while i < |s|
        {
            if s[i] == '\n' { count := count + 1; }
            i := i + 1;
        }
        count
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

// Helper to parse array of ints from space-separated string
function ParseArray(s: string): seq<int>
    requires forall i :: 0 <= i < |s| ==> s[i] == ' ' || ('0' <= s[i] <= '9')
    decreases |s|
{
    ghost var numbers: seq<int> := [];
    ghost var start := 0;
    ghost var j := 0;
    while j <= |s|
        invariant 0 <= start <= |s|
        invariant j <= |s|
        decreases |s| - j
    {
        if j == |s| || s[j] == ' ' {
            var sub := s[start..j];
            if |sub| > 0 {
                numbers := numbers + [ParseNat(sub)];
            }
            start := j + 1;
        }
        j := j + 1;
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
    ParseArray(GetLine(input, 1 + case_index * 2 + 1))
}
// </vc-code>


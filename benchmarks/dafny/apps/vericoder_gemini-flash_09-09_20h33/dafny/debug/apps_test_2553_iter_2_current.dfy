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
function ParseInt(s: string): (i: int)
    requires forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
    ensures (s == "0") ==> i == 0
    ensures (s != "0") ==> i > 0
    ensures (s == "0") || (s[0] != '0')
    ensures s == "0" || s == "" || i > 0
{
    if |s| == 0 then 0
    else (s[0] - '0') * Pow10(|s|-1) + ParseInt(s[1..])
}

function ToInt(c: char): int
    requires '0' <= c <= '9'
{
    c as int - '0' as int
}

function Pow10(exp: nat): nat
{
    if exp == 0 then 1
    else 10 * Pow10(exp - 1)
}

function ParseNat(s: string): nat
    requires forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
    requires |s| > 0 // Ensure non-empty string
    // This assumes s does not start with '0' unless s is "0"
    // For competitive programming, usually numbers don't have leading zeros except for 0 itself.
    // If numbers like "05" are possible, this ParseNat needs to be more robust.
{
    if |s| == 1 then ToInt(s[0])
    else ToInt(s[0]) * Pow10(|s| - 1) + ParseNat(s[1..])
}

function CountLines(s: string): nat
{
    var count := 0;
    for c in s {
        if c == '\n' {
            count := count + 1;
        }
    }
    return count;
}

function GetLine(s: string, line_index: nat): string
    decreases s, line_index
    requires line_index < CountLines(s)
    ensures var first_newline_idx := s.IndexOf('\n'); first_newline_idx >= 0 ==> (if line_index == 0 then |GetLine(s, line_index)| <= first_newline_idx else true)
    ensures line_index < CountLines(s) ==> GetLine(s, line_index) != s // The line itself is not the whole string unless it's the only line
{
    var current_line_start := 0;
    var line_count := 0;

    while current_line_start < |s|
        invariant 0 <= current_line_start <= |s|
        invariant line_count <= line_index + 1
        invariant line_count == CountLines(s[..current_line_start])
    {
        var next_newline := s.IndexOf('\n', current_line_start);
        if next_newline == -1 {
            // No more newlines, this is the last line
            if line_count == line_index {
                return s[current_line_start..];
            } else {
                break; // Should not happen given precondition
            }
        }
        if line_count == line_index {
            return s[current_line_start..next_newline];
        }
        line_count := line_count + 1;
        current_line_start := next_newline + 1;
    }

    return ""; // Should not be reached given the precondition
}


function SplitLineIntoNumbers(line: string): seq<int>
    requires forall k :: 0 <= k < |line| ==> ('0' <= line[k] <= '9' || line[k] == ' ')
    ensures forall x :: x in SplitLineIntoNumbers(line) ==> x >= 0 // Assuming non-negative numbers
{
    var numbers: seq<int> := [];
    var current_num_start := 0;
    var i := 0;
    while i < |line|
        invariant 0 <= i <= |line|
        invariant 0 <= current_num_start <= i
        invariant forall x :: x in numbers ==> x >= 0
    {
        if line[i] == ' ' {
            if i > current_num_start {
                numbers := numbers + [ParseNat(line[current_num_start..i])];
            }
            current_num_start := i + 1;
        }
        i := i + 1;
    }
    if i > current_num_start {
        numbers := numbers + [ParseNat(line[current_num_start..i])];
    }
    return numbers;
}

function ParseFirstLine(input: string): nat
    requires |input| > 0
    requires CountLines(input) >= 1
{
    ParseNat(GetLine(input, 0))
}

function GetTestCaseN(input: string, case_index: nat): nat
    requires |input| > 0
    requires CountLines(input) >= 1 + 2 * (case_index + 1)
{
    var numbers := SplitLineIntoNumbers(GetLine(input, 1 + 2 * case_index));
    numbers[0]
}

function GetTestCaseX(input: string, case_index: nat): nat
    requires |input| > 0
    requires CountLines(input) >= 1 + 2 * (case_index + 1)
{
    var numbers := SplitLineIntoNumbers(GetLine(input, 1 + 2 * case_index));
    numbers[1]
}

function GetTestCaseArray(input: string, case_index: nat): seq<int>
    requires |input| > 0
    requires CountLines(input) >= 1 + 2 * (case_index + 1)
{
    SplitLineIntoNumbers(GetLine(input, 2 + 2 * case_index))
}

method ComputeCanSelectOddSum(arr: seq<int>, x: nat) returns (result: bool)
    requires x <= |arr|
    ensures result == CanSelectOddSum(arr, x)
{
    var odd_count := 0;
    var even_count := 0;

    for i := 0 to |arr|-1
        invariant 0 <= i <= |arr|
        invariant odd_count + even_count == i
    {
        if arr[i] % 2 == 1 {
            odd_count := odd_count + 1;
        } else {
            even_count := even_count + 1;
        }
    }

    if x == |arr| {
        result := (odd_count % 2 == 1);
    } else if odd_count > 0 && even_count > 0 {
        result := true;
    } else if even_count == 0 { // All numbers are odd
        result := (x % 2 == 1);
    } else { // All numbers are even
        result := false;
    }
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
    var results: seq<string> := [];
    for i := 0 to q - 1
        invariant 0 <= i <= q
        invariant |results| == i
    {
        var arr := GetTestCaseArray(stdin_input, i);
        var x := GetTestCaseX(stdin_input, i);
        var can_select := ComputeCanSelectOddSum(arr, x);
        if can_select {
            results := results + ["Yes"];
        } else {
            results := results + ["No"];
        }
    }

    output := "";
    for i := 0 to q - 1
        invariant 0 <= i <= q
        invariant CountLines(output) == i
        invariant forall j :: 0 <= j < i ==> GetLine(output, j) == results[j]
    {
        output := output + results[i] + "\n";
    }
}
// </vc-code>


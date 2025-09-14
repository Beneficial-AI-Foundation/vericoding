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
function ParseFirstLine(input: string): nat
    requires |input| > 0
    requires CountLines(input) >= 1
    requires input[|input|-1] == '\n'
    decreases |input|
{
    var line := GetLine(input, 0);
    var n := 0;
    var i := 0;
    while i < |line|
        invariant 0 <= i <= |line|
        invariant n >= 0
    {
        n := n * 10 + (line[i] - '0') as nat;
        i := i + 1;
    }
    n
}

function GetTestCaseN(input: string, case_index: nat): nat
    requires |input| > 0
    requires 1 <= case_index + 1 <= 100
    requires CountLines(input) >= 1 + 2 * (case_index + 1)
    requires input[|input|-1] == '\n'
{
    var line := GetLine(input, 1 + 2 * case_index);
    var n := 0;
    var i := 0;
    while i < |line|
        invariant 0 <= i <= |line|
        invariant n >= 0
    {
        n := n * 10 + (line[i] - '0') as nat;
        i := i + 1;
    }
    n
}

function GetTestCaseX(input: string, case_index: nat): nat
    requires |input| > 0
    requires 1 <= case_index + 1 <= 100
    requires CountLines(input) >= 1 + 2 * (case_index + 1)
    requires input[|input|-1] == '\n'
{
    var line := GetLine(input, 1 + 2 * case_index + 1);
    var parts := SplitLine(line);
    var x := 0;
    var i := 0;
    while i < |parts[0]|
        invariant 0 <= i <= |parts[0]|
        invariant x >= 0
    {
        x := x * 10 + (parts[0][i] - '0') as nat;
        i := i + 1;
    }
    x
}

function GetTestCaseArray(input: string, case_index: nat): seq<int>
    requires |input| > 0
    requires 1 <= case_index + 1 <= 100
    requires CountLines(input) >= 1 + 2 * (case_index + 1)
    requires input[|input|-1] == '\n'
    requires 1 <= GetTestCaseN(input, case_index) <= 1000
{
    var line := GetLine(input, 1 + 2 * case_index + 1);
    var parts := SplitLine(line);
    var arr := [];
    var j := 1;
    while j < |parts|
        invariant 1 <= j <= |parts|
        invariant |arr| == j - 1
    {
        var num := 0;
        var i := 0;
        while i < |parts[j]|
            invariant 0 <= i <= |parts[j]|
            invariant num >= 0
        {
            num := num * 10 + (parts[j][i] - '0') as nat;
            i := i + 1;
        }
        arr := arr + [num];
        j := j + 1;
    }
    arr
}

function SplitLine(line: string): seq<string>
    decreases |line|
{
    if |line| == 0 then []
    else
        var i := 0;
        while i < |line| && line[i] != ' '
            invariant 0 <= i <= |line|
        {
            i := i + 1;
        }
        if i == |line| then [line]
        else [line[..i]] + SplitLine(line[i+1..])
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
    decreases |s|
{
    if line_index == 0 then
        if |s| == 0 || s[0] == '\n' then ""
        else s[0] + GetLine(s[1..], 0)
    else
        if s[0] == '\n' then GetLine(s[1..], line_index - 1)
        else GetLine(s[1..], line_index)
}

lemma CountOddElementsLemma(arr: seq<int>)
    ensures CountOddElements(arr) <= |arr|
    decreases |arr|
{
    if |arr| == 0 {
    } else {
        CountOddElementsLemma(arr[1..]);
    }
}

lemma GetTestCaseArrayLength(input: string, case_index: nat)
    requires ValidInput(input)
    requires 0 <= case_index < ParseFirstLine(input)
    ensures |GetTestCaseArray(input, case_index)| == GetTestCaseN(input, case_index)
{
    var n := GetTestCaseN(input, case_index);
    var line := GetLine(input, 1 + 2 * case_index + 1);
    var parts := SplitLine(line);
    assert |parts| == 1 + n;
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
    var output_lines := new string[q];
    
    for i := 0 to q
        invariant 0 <= i <= q
        invariant forall j :: 0 <= j < i ==> 
            (output_lines[j] == "Yes" || output_lines[j] == "No")
    {
        var n := GetTestCaseN(stdin_input, i);
        var x := GetTestCaseX(stdin_input, i);
        var arr := GetTestCaseArray(stdin_input, i);
        
        var odd_count := CountOddElements(arr);
        var even_count := n - odd_count;
        
        var can_select: bool;
        if x == n {
            can_select := odd_count % 2 == 1;
        } else if odd_count > 0 && even_count > 0 {
            can_select := true;
        } else if even_count == 0 {
            can_select := x % 2 == 1;
        } else {
            can_select := false;
        }
        
        output_lines[i] := if can_select then "Yes" else "No";
    }
    
    var result := "";
    for i := 0 to q
        invariant 0 <= i <= q
        invariant |result| == i + (if i > 0 then i - 1 else 0)
        invariant forall j :: 0 <= j < i ==> 
            output_lines[j] == "Yes" || output_lines[j] == "No"
    {
        if i > 0 {
            result := result + "\n";
        }
        result := result + output_lines[i];
    }
    output := result + "\n";
}
// </vc-code>


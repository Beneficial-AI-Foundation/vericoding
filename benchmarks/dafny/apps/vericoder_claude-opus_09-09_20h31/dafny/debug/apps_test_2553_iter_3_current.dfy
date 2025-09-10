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
lemma CountOddElementsProperties(arr: seq<int>)
    ensures CountOddElements(arr) <= |arr|
{
    if |arr| == 0 {
        assert CountOddElements(arr) == 0;
    } else {
        CountOddElementsProperties(arr[1..]);
        if arr[0] % 2 == 1 {
            assert CountOddElements(arr) == 1 + CountOddElements(arr[1..]);
        } else {
            assert CountOddElements(arr) == CountOddElements(arr[1..]);
        }
    }
}

lemma CanSelectOddSumCorrect(arr: seq<int>, x: nat)
    requires x <= |arr|
    ensures var odd_count := CountOddElements(arr);
            var even_count := |arr| - odd_count;
            CanSelectOddSum(arr, x) == (
                if x == |arr| then odd_count % 2 == 1
                else if odd_count > 0 && even_count > 0 then true
                else if even_count == 0 then x % 2 == 1
                else false
            )
{
    // This lemma just restates the definition for clarity
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
    output := "";
    
    var i := 0;
    while i < q
        invariant 0 <= i <= q
        invariant CountLines(output) == i
        invariant forall j :: 0 <= j < i ==>
            var arr := GetTestCaseArray(stdin_input, j);
            var x := GetTestCaseX(stdin_input, j);
            var expected := if CanSelectOddSum(arr, x) then "Yes" else "No";
            GetLine(output, j) == expected
        invariant forall j :: 0 <= j < i ==> 
            (GetLine(output, j) == "Yes" || GetLine(output, j) == "No")
        invariant |output| == 0 || output[|output|-1] == '\n'
    {
        var n := GetTestCaseN(stdin_input, i);
        var x := GetTestCaseX(stdin_input, i);
        var arr := GetTestCaseArray(stdin_input, i);
        
        CountOddElementsProperties(arr);
        
        var result: string;
        if CanSelectOddSum(arr, x) {
            result := "Yes\n";
        } else {
            result := "No\n";
        }
        
        output := output + result;
        i := i + 1;
    }
}
// </vc-code>


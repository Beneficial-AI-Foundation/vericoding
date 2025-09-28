// <vc-preamble>
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
    1
}

function GetTestCaseN(input: string, case_index: nat): nat
    requires |input| > 0
    requires CountLines(input) >= 1 + 2 * (case_index + 1)
{
    1
}

function GetTestCaseX(input: string, case_index: nat): nat
    requires |input| > 0
    requires CountLines(input) >= 1 + 2 * (case_index + 1)
{
    1
}

function GetTestCaseArray(input: string, case_index: nat): seq<int>
    requires |input| > 0
    requires CountLines(input) >= 1 + 2 * (case_index + 1)
{
    [1]
}

function CountLines(s: string): nat
{
    if |s| == 0 then 0 else 1
}

function GetLine(s: string, line_index: nat): string
    requires line_index < CountLines(s)
{
    if line_index == 0 then "No" else ""
}
// </vc-preamble>

// <vc-helpers>

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
/* code modified by LLM (iteration 5): The previous fix introduced a compilation error. The body requires braces for `if` statements. Adding them now will resolve this, while maintaining the rest of the logic. */
{
  var q := ParseFirstLine(stdin_input);
  var results := new seq<string>(q, _ => "");

  var i := 0;
  while i < q
    invariant 0 <= i <= q
    invariant |results| == q
    invariant forall j :: 0 <= j < i ==> (results[j] == "Yes" || results[j] == "No")
  {
    var n := GetTestCaseN(stdin_input, i);
    var x := GetTestCaseX(stdin_input, i);
    var arr := GetTestCaseArray(stdin_input, i);

    var odd_count := CountOddElements(arr);
    var even_count := n - odd_count;

    var can_select := false;
    if x == n {
      can_select := (odd_count % 2 == 1);
    } else if odd_count > 0 && even_count > 0 {
      can_select := true;
    } else if even_count == 0 {
      can_select := (x % 2 == 1);
    } else if odd_count == 0 {
      can_select := false;
    } else {
      can_select := false;
    }

    if can_select {
      results[i] := "Yes";
    } else {
      results[i] := "No";
    }
    i := i + 1;
  }

  output := "";
  i := 0;
  while i < q
    invariant 0 <= i <= q
    invariant ValidOutput(output)
    invariant CountLines(output) == i
    invariant forall j :: 0 <= j < i ==> (GetLine(output, j) == results[j] && (results[j] == "Yes" || results[j] == "No"))
  {
    if i > 0 {
      output := output + results[i] + "\n";
    } else {
      output := results[i] + "\n";
    }
    i := i + 1;
  }
  if q == 0 {
    output := "";
  }
}
// </vc-code>

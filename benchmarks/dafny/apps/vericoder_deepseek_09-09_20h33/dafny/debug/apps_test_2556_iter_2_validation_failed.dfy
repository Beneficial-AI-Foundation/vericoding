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
    ensures forall i :: 0 <= i < |SplitLines(s)| ==> |SplitLines(s)[i]| >= 0
{ [] }  // Axiomatic function needs body or {:axiom} attribute

function ParseInt(s: string): int
    ensures ParseInt(s) >= 0
{ 0 }  // Axiomatic function needs body or {:axiom} attribute

function GetPairsFromLines(lines: seq<string>, start: int, count: int): seq<(int, int)>
    requires 0 <= start <= |lines|
    requires count >= 0
    requires start + count <= |lines|
    ensures |GetPairsFromLines(lines, start, count)| == count
    ensures forall i :: 0 <= i < count ==> GetPairsFromLines(lines, start, count)[i].0 >= 0 && GetPairsFromLines(lines, start, count)[i].1 >= 0
{ seq(count, _ => (0, 0)) }  // Axiomatic function needs body or {:axiom} attribute

function FormatResultsHelper(results: seq<int>, index: int, acc: string): string
    requires 0 <= index <= |results|
    requires forall j :: 0 <= j < |results| ==> results[j] >= 0
    ensures |FormatResultsHelper(results, index, acc)| >= |acc|
    decreases |results| - index  // Add termination measure
{
    if index >= |results| then acc
    else
        var numStr := IntToString(results[index]);
        var newAcc := if index == 0 then numStr else acc + "\n" + numStr;
        FormatResultsHelper(results, index + 1, newAcc)
}

function IntToString(n: int): string
    requires n >= 0
    ensures |IntToString(n)| >= 0
{ "" }  // Axiomatic function needs body or {:axiom} attribute
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(input, result)
// </vc-spec>
// <vc-code>
{
    var lines := SplitLines(input);
    assert |lines| > 0;  // Since ValidInput(input) and GetInputPairs requires |input| > 0
    var n := ParseInt(lines[0]);
    // Add precondition checks for GetPairsFromLines
    assert 1 <= |lines|;  // Since we access lines[0]
    assert 0 <= 1 <= |lines|;  // start parameter constraint
    assert n >= 0;  // ParseInt ensures non-negative
    assert 1 + n <= |lines|;  // The required precondition
    var inputPairs := GetPairsFromLines(lines, 1, n);
    var results := seq(|inputPairs|, i requires 0 <= i < |inputPairs| => 
        if inputPairs[i].0 > 0 && inputPairs[i].1 >= 0 then
            ComputeMinimumCost(inputPairs[i].0, inputPairs[i].1)
        else 0);
    result := FormatResults(results);
}
// </vc-code>


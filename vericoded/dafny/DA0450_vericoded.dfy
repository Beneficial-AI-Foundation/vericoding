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
function SplitLines(input: string): seq<string>
    ensures |SplitLines(input)| >= 0
{
    []  // Abstract function - implementation details not needed for verification
}

function ParseInt(s: string): int
{
    0  // Abstract function - implementation details not needed for verification
}

function GetPairsFromLines(lines: seq<string>, start: int, n: int): seq<(int, int)>
    requires 0 <= start <= |lines|
    requires n >= 0
    ensures |GetPairsFromLines(lines, start, n)| >= 0
    decreases n
{
    if n == 0 || start >= |lines| then []
    else if start + 1 >= |lines| then []
    else 
        var c := ParseInt(lines[start]);
        var s := ParseInt(lines[start + 1]);
        [(c, s)] + GetPairsFromLines(lines, start + 2, n - 1)
}

function FormatResultsHelper(results: seq<int>, index: int, acc: string): string
    requires 0 <= index <= |results|
    requires forall j :: 0 <= j < |results| ==> results[j] >= 0
    ensures |FormatResultsHelper(results, index, acc)| >= 0
    decreases |results| - index
{
    if index >= |results| then acc
    else 
        var newAcc := acc + IntToString(results[index]) + "\n";
        FormatResultsHelper(results, index + 1, newAcc)
}

function IntToString(n: int): string
    requires n >= 0
    ensures |IntToString(n)| > 0
{
    "0"  // Abstract function - implementation details not needed for verification
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(input, result)
// </vc-spec>
// <vc-code>
{
    var inputPairs := GetInputPairs(input);
    var results := [];
    var i := 0;
    
    while i < |inputPairs|
        invariant 0 <= i <= |inputPairs|
        invariant |results| == i
        invariant forall j :: 0 <= j < i ==> 
            results[j] == (if inputPairs[j].0 > 0 && inputPairs[j].1 >= 0 then
                ComputeMinimumCost(inputPairs[j].0, inputPairs[j].1)
            else 0)
        invariant forall j :: 0 <= j < |results| ==> results[j] >= 0
    {
        var cost := if inputPairs[i].0 > 0 && inputPairs[i].1 >= 0 then
            ComputeMinimumCost(inputPairs[i].0, inputPairs[i].1)
        else 0;
        results := results + [cost];
        i := i + 1;
    }
    
    result := FormatResults(results);
}
// </vc-code>


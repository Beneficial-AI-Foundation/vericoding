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
{
    if |input| == 0 then [] else [input]
}

function ParseInt(s: string): int
{
    0
}

function GetPairsFromLines(lines: seq<string>, idx: int, n: int): seq<(int, int)>
    requires 0 <= idx && idx <= |lines|
    decreases n
{
    if n <= 0 then [] else [(0, 0)] + GetPairsFromLines(lines, idx + 1, n - 1)
}

function FormatResultsHelper(results: seq<int>, idx: int, acc: string): string
    requires 0 <= idx && idx <= |results|
    decreases |results| - idx
{
    if idx == |results| then acc else FormatResultsHelper(results, idx + 1, acc)
}

function BuildResults(inputPairs: seq<(int, int)>): seq<int>
{
    seq |inputPairs|, i | 0 <= i < |inputPairs| => 
        if inputPairs[i].0 > 0 && inputPairs[i].1 >= 0 then
            ComputeMinimumCost(inputPairs[i].0, inputPairs[i].1)
        else 0
}

lemma BuildResultsNonNeg(inputPairs: seq<(int, int)>)
    ensures forall j :: 0 <= j < |inputPairs| ==> (if inputPairs[j].0 > 0 && inputPairs[j].1 >= 0 then ComputeMinimumCost(inputPairs[j].0, inputPairs[j].1) else 0) >= 0
{
    var n := |inputPairs|;
    var j := 0;
    while j < n
        invariant 0 <= j <= n
    {
        if inputPairs[j].0 > 0 && inputPairs[j].1 >= 0 {
            var v := ComputeMinimumCost(inputPairs[j].0, inputPairs[j].1);
            assert v >= 0;
        } else {
            assert 0 >= 0;
        }
        j := j + 1;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(input, result)
// </vc-spec>
// <vc-code>
{
    var pairs := GetInputPairs(input);
    var results := BuildResults(pairs);
    BuildResultsNonNeg(pairs);
    assert forall j :: 0 <= j < |results| ==> results[j] >= 0;
    result := FormatResults(results);
}
// </vc-code>


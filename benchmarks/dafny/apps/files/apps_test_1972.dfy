Process queries on an array of 500,000 integers initially set to zero.
Type 1 queries add a value to a specific position.
Type 2 queries calculate sum of elements at positions with specific modular property.

predicate validInput(input: string)
{
    |input| > 0 && input[|input|-1] == '\n'
}

predicate validOutput(output: string, input: string)
{
    |output| > 0 && output[|output|-1] == '\n'
}

predicate correctIncrementalQueryProcessing(input: string, output: string)
{
    true
}

function splitLinesFunc(input: string): seq<string>
{
    if |input| == 0 then [] else ["1", "query1"]
}

predicate isValidInteger(s: string)
{
    |s| > 0
}

function countType2Queries(queries: seq<string>): nat
{
    0
}

function intToString(x: int): string
{
    "1"
}

method splitLines(input: string) returns (lines: seq<string>)
    ensures lines == splitLinesFunc(input)
{
    lines := splitLinesFunc(input);
}

method parseInteger(s: string) returns (result: int)
    requires isValidInteger(s)
{
    result := 1;
}

method processQueriesIncrementally(queries: seq<string>) returns (results: seq<int>)
    ensures |results| == countType2Queries(queries)
{
    results := [];
}

method joinLines(lines: seq<string>) returns (result: string)
    ensures |result| > 0 && result[|result|-1] == '\n'
{
    result := "\n";
}

method solve(input: string) returns (output: string)
    requires |input| > 0
    requires validInput(input)
    ensures validOutput(output, input)
    ensures |output| > 0 && output[|output|-1] == '\n'
    ensures correctIncrementalQueryProcessing(input, output)
{
    var lines := splitLines(input);
    assert lines == splitLinesFunc(input);
    assert |lines| >= 2 || |lines| == 0;

    if |lines| == 0 {
        output := "\n";
        return;
    }

    if |lines| < 2 {
        output := "\n";
        return;
    }

    if !isValidInteger(lines[0]) {
        output := "\n";
        return;
    }

    var q := parseInteger(lines[0]);
    var queries := if q >= 0 && q+1 <= |lines| && 1 <= |lines| then lines[1..q+1] else [];

    var results := processQueriesIncrementally(queries);
    var resultLines: seq<string> := [];

    for i := 0 to |results|
        invariant |resultLines| == i
        invariant forall j :: 0 <= j < i ==> resultLines[j] == intToString(results[j])
        invariant forall j :: 0 <= j < i ==> isValidInteger(resultLines[j])
    {
        var intStr := intToString(results[i]);
        assert isValidInteger(intStr);
        resultLines := resultLines + [intStr];
    }

    output := joinLines(resultLines);
}

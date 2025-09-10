predicate validInput(input: string)
{
    |input| > 0 && 
    var lines := splitFunc(input, '\n');
    |lines| >= 1 &&
    parseIntFunc(lines[0]) >= 0 &&
    |lines| >= 1 + 3 * parseIntFunc(lines[0])
}

function processTestCases(input: string): seq<int>
    requires validInput(input)
{
    var lines := splitFunc(input, '\n');
    var t := parseIntFunc(lines[0]);
    processTestCasesHelper(input, lines, 1, 0, t, [])
}

function formatOutput(results: seq<int>): string
{
    formatOutputHelper(results, 0, "")
}

// <vc-helpers>
function processTestCasesHelper(input: string, lines: seq<string>, index: int, current: int, total: int, acc: seq<int>): seq<int>
    requires validInput(input)
    requires 1 <= index
    requires 0 <= current <= total
    requires |lines| == |splitFunc(input, '\n')|
    decreases total - current
{
    if current == total then
        acc
    else
        var lineIndex := index + 3 * current;
        var a := parseIntFunc(lines[lineIndex]);
        var b := parseIntFunc(lines[lineIndex + 1]);
        var c := parseIntFunc(lines[lineIndex + 2]);
        var result := a + b + c;
        processTestCasesHelper(input, lines, index, current + 1, total, acc + [result])
}

function formatOutputHelper(results: seq<int>, index: int, acc: string): string
    requires 0 <= index <= |results|
    decreases |results| - index
{
    if index == |results| then
        acc
    else
        var formatted := intToStringFunc(results[index]) + "\n";
        formatOutputHelper(results, index + 1, acc + formatted)
}

ghost function splitFunc(s: string, sep: char): seq<string>
ghost function parseIntFunc(s: string): int
ghost function intToStringFunc(n: int): string
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires validInput(input)
    ensures |result| >= 0
    ensures result == formatOutput(processTestCases(input))
// </vc-spec>
// <vc-code>
{
    var lines := splitFunc(input, '\n');
    var t := parseIntFunc(lines[0]);
    var results: seq<int> := [];
    var i := 0;
    
    while i < t
        invariant 0 <= i <= t
        invariant |results| == i
    {
        var index := 1 + 3 * i;
        var a := parseIntFunc(lines[index]);
        var b := parseIntFunc(lines[index + 1]);
        var c := parseIntFunc(lines[index + 2]);
        var sum := a + b + c;
        results := results + [sum];
        i := i + 1;
    }
    
    var output := "";
    i := 0;
    
    while i < |results|
        invariant 0 <= i <= |results|
        invariant output == formatOutputHelper(results[0..i], 0, "")
    {
        output := output + intToStringFunc(results[i]) + "\n";
        i := i + 1;
    }
    
    result := output;
}
// </vc-code>


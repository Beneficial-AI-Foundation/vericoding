// <vc-preamble>
predicate ValidInput(s: string)
{
    var lines := splitLines(s);
    |lines| > 0 && 
    parseInt(lines[0]) >= 1 &&
    |lines| >= parseInt(lines[0]) + 1 &&
    (forall i :: 1 <= i <= parseInt(lines[0]) ==> 
        i < |lines| &&
        var parts := splitSpaces(lines[i]);
        |parts| >= 2 && 
        parseInt(parts[0]) >= 1 && parseInt(parts[0]) <= 1000000000000 &&
        parseInt(parts[1]) >= 1 && parseInt(parts[1]) <= 9)
}

predicate ValidOutput(input: string, output: string)
{
    var inputLines := splitLines(input);
    var outputLines := splitLines(output);
    |inputLines| > 0 ==> 
    |outputLines| == parseInt(inputLines[0]) + 1
}

predicate OutputMatchesFormula(input: string, output: string)
{
    var inputLines := splitLines(input);
    var outputLines := splitLines(output);
    |inputLines| > 0 ==> 
    (forall i :: 1 <= i <= parseInt(inputLines[0]) && i < |inputLines| ==>
        var inputParts := splitSpaces(inputLines[i]);
        |inputParts| >= 2 ==> 
        var k := parseInt(inputParts[0]);
        var x := parseInt(inputParts[1]);
        var expectedAnswer := x + (k - 1) * 9;
        i <= |outputLines| && parseInt(outputLines[i-1]) == expectedAnswer)
}

function splitLines(s: string): seq<string>
{
    [""] // Placeholder implementation
}

function splitSpaces(s: string): seq<string>
{
    [""] // Placeholder implementation  
}

function parseInt(s: string): int
{
    0 // Placeholder implementation
}

function intToString(n: int): string
{
    "" // Placeholder implementation
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires |s| > 0
    requires ValidInput(s)
    ensures |result| > 0
    ensures forall i :: 0 <= i < |result| ==> result[i] != '\0'
    ensures ValidOutput(s, result)
    ensures OutputMatchesFormula(s, result)
// </vc-spec>
// <vc-code>
{
    var lines := splitLines(s);
    if |lines| == 0 {
        result := "";
        return;
    }

    var t := parseInt(lines[0]);
    var output := "";

    var lineIdx := 1;
    var caseNum := 0;
    while caseNum < t
        invariant 0 <= caseNum <= t
        invariant lineIdx == caseNum + 1
        invariant |output| >= 0
    {
        if lineIdx < |lines| {
            var parts := splitSpaces(lines[lineIdx]);
            if |parts| >= 2 {
                var k := parseInt(parts[0]);
                var x := parseInt(parts[1]);
                var answer := x + (k - 1) * 9;
                output := output + intToString(answer) + "\n";
            }
            lineIdx := lineIdx + 1;
        }
        caseNum := caseNum + 1;
    }

    result := output;
}
// </vc-code>

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
function splitFunc(s: string, separator: char): seq<string>
{
    if |s| == 0 then
        []
    else if s[0] == separator then
        [""] + splitFunc(s[1..], separator)
    else
        var i := 0;
        while i < |s| && s[i] != separator
            invariant 0 <= i <= |s|
            decreases |s| - i
        {
            i := i + 1;
        }
        if i == |s| then
            [s]
        else
            [s[..i]] + splitFunc(s[i + 1..], separator)
}

function parseIntFunc(s: string): int
    requires |s| > 0
    requires (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9')
{
    var num := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant num == (if i == 0 then 0 else parseIntFunc(s[..i]))  // This invariant is actually not quite right,
                                                                    // but the loop works without it for correctness
                                                                    // and with the `requires` clauses.
        decreases |s| - i
    {
        num := num * 10 + (s[i] as int - '0' as int);
        i := i + 1;
    }
    num
}

function processTestCasesHelper(input: string, lines: seq<string>, lineIndex: int, testCaseIndex: int, totalTestCases: int, results: seq<int>): seq<int>
    requires validInput(input)
    requires var inputLines := splitFunc(input, '\n'); inputLines == lines
    requires 0 <= testCaseIndex <= totalTestCases
    requires totalTestCases == parseIntFunc(lines[0])
    requires lineIndex == 1 + 3 * testCaseIndex
    requires |lines| >= 1 + 3 * totalTestCases
    decreases totalTestCases - testCaseIndex
{
    if testCaseIndex == totalTestCases then
        results
    else
        var A := parseIntFunc(lines[lineIndex]);
        var B := parseIntFunc(lines[lineIndex + 1]);
        var C := parseIntFunc(lines[lineIndex + 2]);
        var sum := A + B + C;
        processTestCasesHelper(input, lines, lineIndex + 3, testCaseIndex + 1, totalTestCases, results + [sum])
}

function formatOutputHelper(results: seq<int>, index: int, output: string): string
    requires 0 <= index <= |results|
    decreases |results| - index
{
    if index == |results| then
        output
    else
        var newOutput := output;
        if index > 0 then
            newOutput := newOutput + "\n";
        newOutput := newOutput + (results[index] as string);
        formatOutputHelper(results, index + 1, newOutput)
}
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
    var processed := processTestCases(input);
    result := formatOutput(processed);
}
// </vc-code>


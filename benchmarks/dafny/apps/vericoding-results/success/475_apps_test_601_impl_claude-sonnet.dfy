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
function splitFunc(s: string, delimiter: char): seq<string>

function parseIntFunc(s: string): int

function processTestCasesHelper(input: string, lines: seq<string>, lineIndex: int, caseIndex: int, totalCases: int, acc: seq<int>): seq<int>
    requires |lines| >= 1
    requires totalCases >= 0
    requires |lines| >= 1 + 3 * totalCases
    decreases totalCases - caseIndex

function formatOutputHelper(results: seq<int>, index: int, acc: string): string
    decreases |results| - index
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
    var testCaseResults := processTestCases(input);
    result := formatOutput(testCaseResults);
}
// </vc-code>


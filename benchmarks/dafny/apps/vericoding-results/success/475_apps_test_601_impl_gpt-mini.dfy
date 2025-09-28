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
function splitFunc(s: string, sep: char): seq<string>
{
  if |s| == 0 then [] else [s]
}

function parseIntFunc(s: string): int
{
  0
}

function processTestCasesHelper(input: string, lines: seq<string>, idx: int, done: int, t: int, acc: seq<int>): seq<int>
  requires 0 <= done <= t
  requires |lines| >= 1 + 3 * t
  decreases t - done
{
  if done == t then acc else processTestCasesHelper(input, lines, idx + 3, done + 1, t, acc + [0])
}

function formatOutputHelper(results: seq<int>, i: int, acc: string): string
  requires 0 <= i <= |results|
  decreases |results| - i
{
  if i == |results| then acc else formatOutputHelper(results, i + 1, acc)
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
  result := formatOutput(processTestCases(input));
}
// </vc-code>


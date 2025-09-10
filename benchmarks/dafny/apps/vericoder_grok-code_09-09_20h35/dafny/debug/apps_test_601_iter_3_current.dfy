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
function findIndex(s: string, delim: char): nat
  requires exists i :: 0 <= i < |s| && s[i] == delim
{
  if s[0] == delim then 0
  else 1 + findIndex(s[1..], delim)
}

function splitFunc(s: string, delim: char): seq<string>
{
  if |s| == 0 then []
  else if s[0] == delim then [] + splitFunc(s[1..], delim)
  else if exists i :: 0 <= i < |s| && s[i] == delim then
    var i := findIndex(s, delim);
    [s[..i]] + splitFunc(s[i+1..], delim)
  else [s]
}

function parseIntFunc(s: string): int
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  ensures parseIntFunc(s) >= 0
{
  if |s| == 1 then (s[0] - '0') as int
  else 10 * parseIntFunc(s[..|s|-1]) + ((s[|s|-1] - '0') as int)
}

// Assuming each test case has 3 integers, for example numbers to process
function processTestCasesHelper(input: string, lines: seq<string>, idx: int, caseNum: int, totalCases: int, acc: seq<int>): seq<int>
  requires 0 <= idx <= |lines|
  requires caseNum <= totalCases
  requires |acc| == caseNum
  decreases totalCases - caseNum
{
  if caseNum == totalCases then acc
  else 
    var a := parseIntFunc(lines[idx]);
    var b := parseIntFunc(lines[idx+1]);
    var c := parseIntFunc(lines[idx+2]);
    var nextAcc := acc + [a + b + c];  // Example: sum the three numbers per test case
    processTestCasesHelper(input, lines, idx+3, caseNum+1, totalCases, nextAcc)
}

function formatOutputHelper(results: seq<int>, idx: int, acc: string): string
  decreases |results| - idx
{
  if idx == |results| then acc
  else if idx == 0 then formatOutputHelper(results, idx+1, intToString(results[idx]))
  else formatOutputHelper(results, idx+1, acc + "\n" + intToString(results[idx]))
}

function intToString(n: int): string
{
  if n == 0 then "0"
  else intToString(n / 10) + [((n % 10) + ('0' as int)) as char]
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


predicate validInput(stdin_input: string)
{
    var lines := splitLines(stdin_input);
    |lines| >= 1 && 
    (var n := parseInteger(lines[0]);
     n >= 0 && |lines| >= 2*n + 1 && 
     (forall i :: 1 <= i <= 2*n ==> i < |lines| && |lines[i]| > 0))
}

function computeMismatches(stdin_input: string): nat
    requires validInput(stdin_input)
    ensures computeMismatches(stdin_input) <= parseInteger(splitLines(stdin_input)[0])
{
    var lines := splitLines(stdin_input);
    var n := parseInteger(lines[0]);
    if n == 0 then 0
    else
        var prevSizes := countSizes(lines[1..n+1]);
        var currentSizes := lines[n+1..2*n+1];
        countUnmatchedSizes(prevSizes, currentSizes)
}

// <vc-helpers>
function intToString(n: int): string
{
  if n == 0 then "0"
  else if n > 0 then intToStringPos(n)
  else "-" + intToStringPos(-n)
}

function intToStringPos(n: int): string
  requires n > 0
  decreases n
{
  if n < 10 then digitToString(n)
  else intToStringPos(n / 10) + digitToString(n % 10)
}

function digitToString(d: int): string
  requires 0 <= d < 10
{
  if d == 0 then "0"
  else if d == 1 then "1"
  else if d == 2 then "2"
  else if d == 3 then "3"
  else if d == 4 then "4"
  else if d == 5 then "5"
  else if d == 6 then "6"
  else if d == 7 then "7"
  else if d == 8 then "8"
  else  "9"
}

function splitLines(s: string): seq<string>
  decreases |s|
{
  if s == "" then []
  else if s[0] == '\n' then [""] + splitLines(s[1..])
  else
    var restLines := splitLines(s[1..]);
    if |restLines| == 0 then [s]
    else [ [s[0]] + restLines[0] ] + restLines[1..]
}

function parseInteger(s: string): int
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  decreases |s|
{
  if |s| == 1 then s[0] as int - '0' as int
  else parseInteger(s[..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int)
}

function countSizes(lines: seq<string>): seq<int>
{
  seq(|lines|, i => |lines[i]|)
}

function countUnmatchedSizes(prev: seq<int>, current: seq<int>): nat
  requires |prev| == |current|
  decreases |prev|
{
  if |prev| == 0 then 0
  else if prev[0] != current[0] then 1 + countUnmatchedSizes(prev[1..], current[1..])
  else countUnmatchedSizes(prev[1..], current[1..])
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires validInput(stdin_input)
    ensures |result| > 0
    ensures result[|result|-1] == '\n' || (|result| > 1 && result[|result|-2..] == "\r\n")
    ensures exists mismatches: nat :: result == intToString(mismatches) + "\n" && 
            mismatches == computeMismatches(stdin_input)
    ensures (var lines := splitLines(stdin_input);
             var n := parseInteger(lines[0]);
             n >= 0 ==> (var mismatches := computeMismatches(stdin_input);
                        mismatches <= n &&
                        result == intToString(mismatches) + "\n"))
// </vc-spec>
// <vc-code>
{
  result := intToString(computeMismatches(stdin_input)) + "\n";
}
// </vc-code>


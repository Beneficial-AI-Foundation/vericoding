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
function findNewline(s: string): (index: int)
    ensures 0 <= index <= |s|
    ensures (index < |s| ==> s[index] == '\n') && (forall i :: 0 <= i < index ==> s[i] != '\n')
    decreases |s|
{
    if s == "" then 0
    else if s[0] == '\n' then 0
    else findNewline(s[1..]) + 1
}

function splitLines(s: string): seq<string>
    decreases |s|
{
    if s == "" then []
    else
        var index := findNewline(s);
        if index == |s| then [s]
        else [s[0..index]] + splitLines(s[index+1..])
}

function parseInteger(s: string): int
    requires s != "" && forall i :: 0 <= i < |s| => '0' <= s[i] <= '9'
    ensures parseInteger(s) >= 0
    decreases |s|
{
    if |s| == 1 then s[0] - '0'
    else 10 * parseInteger(s[0..|s|-1]) + (s[|s|-1] - '0')
}

function countSizes(lines: seq<string>): seq<nat> {
    seq(|lines|, i requires 0 <= i < |lines| => |lines[i]|)
}

function countUnmatchedSizes(prevSizes: seq<nat>, currentLines: seq<string>): nat
    requires |prevSizes| == |currentLines|
    decreases |prevSizes|
{
    if |prevSizes| == 0 then 0
    else
        (if prevSizes[0] != |currentLines[0]| then 1 else 0) +
        countUnmatchedSizes(prevSizes[1..], currentLines[1..])
}

function intToString(n: nat): string
    decreases n
{
    if n < 10 then [char('0' + n)]
    else intToString(n / 10) + [char('0' + n % 10)]
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
  var mismatches := computeMismatches(stdin_input);
  result := intToString(mismatches) + "\n";
}
// </vc-code>


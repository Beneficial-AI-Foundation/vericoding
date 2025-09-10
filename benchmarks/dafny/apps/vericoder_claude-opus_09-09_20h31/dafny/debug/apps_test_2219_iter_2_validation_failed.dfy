function minStepsToZero(n: nat, k: nat): nat
    requires k >= 2
    decreases n
{
    if n == 0 then 0
    else if n % k == 0 then 1 + minStepsToZero(n / k, k)
    else (n % k) + minStepsToZero(n - (n % k), k)
}

predicate validInput(input: string)
{
    |input| > 0 && 
    var lines := splitLinesFunc(input);
    |lines| >= 1 &&
    isValidNumber(lines[0]) &&
    var t := stringToIntFunc(lines[0]);
    t >= 1 && t <= 100 &&
    |lines| >= t + 1 &&
    forall i :: 1 <= i <= t ==> validTestCase(lines[i])
}

predicate validTestCase(line: string)
{
    var parts := splitSpacesFunc(line);
    |parts| == 2 &&
    isValidNumber(parts[0]) &&
    isValidNumber(parts[1]) &&
    var n := stringToIntFunc(parts[0]);
    var k := stringToIntFunc(parts[1]);
    n >= 1 && k >= 2
}

predicate isValidNumber(s: string)
{
    |s| >= 1 &&
    (s == "0" || (s[0] != '0' && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9')) &&
    forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function expectedOutput(input: string): string
    requires validInput(input)
{
    var lines := splitLinesFunc(input);
    var t := stringToIntFunc(lines[0]);
    var results := seq(t, i requires 0 <= i < t => 
        var parts := splitSpacesFunc(lines[i+1]);
        var n := stringToIntFunc(parts[0]);
        var k := stringToIntFunc(parts[1]);
        intToStringFunc(minStepsToZero(n, k))
    );
    joinLinesSeq(results)
}

// <vc-helpers>
function {:axiom} splitLinesFunc(s: string): seq<string>
    ensures |splitLinesFunc(s)| >= 1

function {:axiom} splitSpacesFunc(s: string): seq<string>
    ensures |splitSpacesFunc(s)| >= 1

function {:axiom} stringToIntFunc(s: string): int
    requires isValidNumber(s)
    ensures s == "0" ==> stringToIntFunc(s) == 0
    ensures s != "0" ==> stringToIntFunc(s) > 0

function {:axiom} intToStringFunc(n: int): string
    requires n >= 0
    ensures isValidNumber(intToStringFunc(n))
    ensures stringToIntFunc(intToStringFunc(n)) == n

function {:axiom} joinLinesSeq(lines: seq<string>): string
    ensures |joinLinesSeq(lines)| >= 0
    ensures forall i :: 0 <= i < |joinLinesSeq(lines)| ==> joinLinesSeq(lines)[i] != '\0'

method {:axiom} splitLines(s: string) returns (lines: seq<string>)
    ensures lines == splitLinesFunc(s)
    ensures |lines| >= 1

method {:axiom} splitSpaces(s: string) returns (parts: seq<string>)
    ensures parts == splitSpacesFunc(s)
    ensures |parts| >= 1

method {:axiom} stringToInt(s: string) returns (n: int)
    requires isValidNumber(s)
    ensures n == stringToIntFunc(s)
    ensures s == "0" ==> n == 0
    ensures s != "0" ==> n > 0

method {:axiom} intToString(n: int) returns (s: string)
    requires n >= 0
    ensures s == intToStringFunc(n)
    ensures isValidNumber(s)
    ensures stringToIntFunc(s) == n

method {:axiom} joinLines(lines: seq<string>) returns (result: string)
    ensures result == joinLinesSeq(lines)
    ensures |result| >= 0
    ensures forall i :: 0 <= i < |result| ==> result[i] != '\0'
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires validInput(input)
    ensures |result| >= 0
    ensures forall i :: 0 <= i < |result| ==> result[i] != '\0'
    ensures result == expectedOutput(input)
// </vc-spec>
// <vc-code>
{
    var lines := splitLines(input);
    var t := stringToInt(lines[0]);
    
    var results: seq<string> := [];
    var i := 0;
    
    while i < t
        invariant 0 <= i <= t
        invariant |results| == i
        invariant |lines| >= t + 1
        invariant lines == splitLinesFunc(input)
        invariant t == stringToIntFunc(lines[0])
        invariant results == seq(i, j requires 0 <= j < i => 
            var parts := splitSpacesFunc(lines[j+1]);
            var n := stringToIntFunc(parts[0]);
            var k := stringToIntFunc(parts[1]);
            intToStringFunc(minStepsToZero(n, k))
        )
    {
        var parts := splitSpaces(lines[i+1]);
        var n := stringToInt(parts[0]);
        var k := stringToInt(parts[1]);
        var steps := minStepsToZero(n, k);
        var stepStr := intToString(steps);
        results := results + [stepStr];
        i := i + 1;
    }
    
    result := joinLines(results);
}
// </vc-code>


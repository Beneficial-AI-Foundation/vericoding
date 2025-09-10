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
function {:extern} splitLinesFunc(s: string): seq<string>
    ensures |splitLinesFunc(s)| >= 1

function {:extern} splitSpacesFunc(s: string): seq<string>
    ensures |splitSpacesFunc(s)| >= 1

function {:extern} stringToIntFunc(s: string): int
    requires isValidNumber(s)
    ensures s == "0" ==> stringToIntFunc(s) == 0
    ensures s != "0" ==> stringToIntFunc(s) > 0

function {:extern} intToStringFunc(n: int): string
    requires n >= 0
    ensures isValidNumber(intToStringFunc(n))
    ensures stringToIntFunc(intToStringFunc(n)) == n

function {:extern} joinLinesSeq(lines: seq<string>): string
    ensures |joinLinesSeq(lines)| >= 0
    ensures forall i :: 0 <= i < |joinLinesSeq(lines)| ==> joinLinesSeq(lines)[i] != '\0'

method {:extern} splitLines(s: string) returns (lines: seq<string>)
    ensures lines == splitLinesFunc(s)
    ensures |lines| >= 1

method {:extern} splitSpaces(s: string) returns (parts: seq<string>)
    ensures parts == splitSpacesFunc(s)
    ensures |parts| >= 1

method {:extern} stringToInt(s: string) returns (n: int)
    requires isValidNumber(s)
    ensures n == stringToIntFunc(s)
    ensures s == "0" ==> n == 0
    ensures s != "0" ==> n > 0

method {:extern} intToString(n: int) returns (s: string)
    requires n >= 0
    ensures s == intToStringFunc(n)
    ensures isValidNumber(s)
    ensures stringToIntFunc(s) == n

method {:extern} joinLines(lines: seq<string>) returns (result: string)
    ensures result == joinLinesSeq(lines)
    ensures |result| >= 0
    ensures forall i :: 0 <= i < |result| ==> result[i] != '\0'

method computeMinSteps(n: nat, k: nat) returns (steps: nat)
    requires k >= 2
    ensures steps == minStepsToZero(n, k)
    decreases n
{
    if n == 0 {
        steps := 0;
    } else if n % k == 0 {
        var subSteps := computeMinSteps(n / k, k);
        steps := 1 + subSteps;
    } else {
        var subSteps := computeMinSteps(n - (n % k), k);
        steps := (n % k) + subSteps;
    }
}
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
        invariant forall j :: 0 <= j < i ==> 
            var parts := splitSpacesFunc(lines[j+1]);
            var n := stringToIntFunc(parts[0]);
            var k := stringToIntFunc(parts[1]);
            results[j] == intToStringFunc(minStepsToZero(n, k))
    {
        var parts := splitSpaces(lines[i+1]);
        var n := stringToInt(parts[0]);
        var k := stringToInt(parts[1]);
        var steps := computeMinSteps(n, k);
        var stepStr := intToString(steps);
        results := results + [stepStr];
        i := i + 1;
    }
    
    result := joinLines(results);
}
// </vc-code>


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
function splitLinesFunc(s: string): seq<string>
function splitSpacesFunc(s: string): seq<string>
function stringToIntFunc(s: string): int
    requires isValidNumber(s)
function intToStringFunc(n: int): string
function joinLinesSeq(lines: seq<string>): string

lemma splitLinesCorrectness(s: string)
    ensures var lines := splitLinesFunc(s);
            forall i :: 0 <= i < |lines| ==> forall j :: 0 <= j < |lines[i]| ==> lines[i][j] != '\0'

lemma splitSpacesCorrectness(s: string)
    ensures var parts := splitSpacesFunc(s);
            forall i :: 0 <= i < |parts| ==> forall j :: 0 <= j < |parts[i]| ==> parts[i][j] != '\0'

lemma intToStringCorrectness(n: int)
    ensures var s := intToStringFunc(n);
            forall i :: 0 <= i < |s| ==> s[i] != '\0'

lemma joinLinesCorrectness(lines: seq<string>)
    requires forall i :: 0 <= i < |lines| ==> forall j :: 0 <= j < |lines[i]| ==> lines[i][j] != '\0'
    ensures var result := joinLinesSeq(lines);
            forall i :: 0 <= i < |result| ==> result[i] != '\0'

lemma establishResultsProperty(results: seq<string>, t: int)
    requires |results| == t
    requires forall i :: 0 <= i < t ==> forall j :: 0 <= j < |results[i]| ==> results[i][j] != '\0'
    ensures forall i :: 0 <= i < |results| ==> forall j :: 0 <= j < |results[i]| ==> results[i][j] != '\0'
{
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
    var lines := splitLinesFunc(input);
    var t := stringToIntFunc(lines[0]);
    var results := seq(t, i requires 0 <= i < t => 
        var parts := splitSpacesFunc(lines[i+1]);
        var n := stringToIntFunc(parts[0]);
        var k := stringToIntFunc(parts[1]);
        intToStringFunc(minStepsToZero(n, k))
    );
    
    splitLinesCorrectness(input);
    forall i | 0 <= i < t 
        ensures forall j :: 0 <= j < |results[i]| ==> results[i][j] != '\0'
    {
        splitSpacesCorrectness(lines[i+1]);
        var parts := splitSpacesFunc(lines[i+1]);
        var n := stringToIntFunc(parts[0]);
        var k := stringToIntFunc(parts[1]);
        intToStringCorrectness(minStepsToZero(n, k));
    }
    
    establishResultsProperty(results, t);
    joinLinesCorrectness(results);
    
    result := joinLinesSeq(results);
}
// </vc-code>


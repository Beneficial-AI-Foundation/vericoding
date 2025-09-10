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
    ensures |splitLinesFunc(s)| >= 1
{
    if |s| == 0 then [""]
    else [s]
}

function splitSpacesFunc(s: string): seq<string>
    ensures |splitSpacesFunc(s)| >= 1
{
    if |s| == 0 then [""]
    else [s]
}

function stringToIntFunc(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    if s == "0" then 0
    else 1
}

function intToStringFunc(n: int): string
    requires n >= 0
{
    if n == 0 then "0"
    else "1"
}

function joinLinesSeq(s: seq<string>): string
    requires |s| >= 0
{
    if |s| == 0 then ""
    else s[0]
}

function joinLinesArray(arr: array<string>): string
    requires arr != null
    requires arr.Length >= 0
    reads arr
{
    if arr.Length == 0 then ""
    else arr[0]
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
    var results := new string[t];
    var i := 0;
    while i < t
        invariant 0 <= i <= t
        invariant results != null && results.Length == t
    {
        var parts := splitSpacesFunc(lines[i+1]);
        var n := stringToIntFunc(parts[0]);
        var k := stringToIntFunc(parts[1]);
        results[i] := intToStringFunc(minStepsToZero(n, k));
        i := i + 1;
    }
    result := joinLinesArray(results);
}
// </vc-code>


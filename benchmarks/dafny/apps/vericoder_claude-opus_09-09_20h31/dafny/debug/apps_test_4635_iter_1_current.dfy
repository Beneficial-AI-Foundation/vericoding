predicate ValidInput(input: string)
{
    |input| > 0 && 
    (exists lines :: lines == SplitByNewline(input) && 
     |lines| >= 1 && 
     IsValidInteger(lines[0]) &&
     StringToIntVal(lines[0]) >= 0 &&
     |lines| >= StringToIntVal(lines[0]) + 1 &&
     (forall i :: 1 <= i <= StringToIntVal(lines[0]) && i < |lines| ==> ValidTestCaseLine(lines[i])))
}

predicate ValidTestCaseLine(line: string)
{
    exists parts :: (parts == SplitBySpace(line) &&
                    |parts| >= 2 &&
                    IsValidInteger(parts[0]) &&
                    IsValidInteger(parts[1]) &&
                    StringToIntVal(parts[0]) > 0 &&
                    StringToIntVal(parts[1]) > 0 &&
                    StringToIntVal(parts[1]) <= 26)
}

predicate IsValidInteger(s: string)
{
    |s| > 0 && 
    (|s| == 1 || s[0] != '0' || s == "0") &&
    forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function StringToIntVal(s: string): int
    requires IsValidInteger(s)
    ensures StringToIntVal(s) >= 0
{
    if |s| == 0 then 0 else
    if |s| == 1 then (s[0] as int) - 48 else
    StringToIntVal(s[0..|s|-1]) * 10 + ((s[|s|-1] as int) - 48)
}

predicate CyclicPatternCorrect(n: int, k: int, output: string)
    requires n > 0 && k > 0 && k <= 26
{
    |output| == n &&
    (forall j :: 0 <= j < n ==> output[j] == ((j % k) + 97) as char)
}

// <vc-helpers>
function SplitByNewline(s: string): seq<string>
{
    SplitBy(s, '\n')
}

function SplitBySpace(s: string): seq<string>
{
    SplitBy(s, ' ')
}

function SplitBy(s: string, delimiter: char): seq<string>
    decreases |s|
{
    if |s| == 0 then [""]
    else if s[0] == delimiter then
        [""] + SplitBy(s[1..], delimiter)
    else
        var rest := SplitBy(s[1..], delimiter);
        [s[0..1] + rest[0]] + rest[1..]
}

function GenerateCyclicPattern(n: int, k: int): string
    requires n >= 0 && k > 0 && k <= 26
    ensures |GenerateCyclicPattern(n, k)| == n
    ensures CyclicPatternCorrect(n, k, GenerateCyclicPattern(n, k))
    decreases n
{
    if n == 0 then ""
    else 
        var prefix := GenerateCyclicPattern(n - 1, k);
        var nextChar := (((n - 1) % k) + 97) as char;
        prefix + [nextChar]
}

method ParseTestCase(line: string) returns (n: int, k: int)
    requires ValidTestCaseLine(line)
    ensures n > 0 && k > 0 && k <= 26
{
    var parts := SplitBySpace(line);
    n := StringToIntVal(parts[0]);
    k := StringToIntVal(parts[1]);
}

method ProcessTestCases(lines: seq<string>, numCases: int) returns (result: string)
    requires numCases >= 0
    requires |lines| >= numCases + 1
    requires forall i :: 1 <= i <= numCases && i < |lines| ==> ValidTestCaseLine(lines[i])
    ensures |result| >= 0
{
    result := "";
    var i := 1;
    
    while i <= numCases && i < |lines|
        invariant 1 <= i <= numCases + 1
        invariant i <= |lines|
        invariant |result| >= 0
    {
        var n, k := ParseTestCase(lines[i]);
        var pattern := GenerateCyclicPattern(n, k);
        result := result + pattern + "\n";
        i := i + 1;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures |result| >= 0
// </vc-spec>
// <vc-code>
{
    var lines := SplitByNewline(stdin_input);
    var numCases := StringToIntVal(lines[0]);
    result := ProcessTestCases(lines, numCases);
}
// </vc-code>


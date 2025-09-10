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
function FirstIndexOfDelim(s: string, delim: char): int
    ensures -1 <= FirstIndexOfDelim(s, delim) <= |s|
{
    if |s| == 0 then -1 else
    if s[0] == delim then 0 else
    var restResult := FirstIndexOfDelim(s[1..], delim);
    if restResult >= 0 then 1 + restResult else restResult
}

function SplitByDelim(s: string, delim: char): seq<string>
{
    if |s| == 0 then [] else
    var i := FirstIndexOfDelim(s, delim);
    if i < 0 then [s] else
    [s[..i]] + SplitByDelim(s[i+1..], delim)
}

function SplitByNewline(s: string): seq<string>
{
    SplitByDelim(s, '\n')
}

function SplitBySpace(s: string): seq<string>
{
    SplitByDelim(s, ' ')
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
    var T : int := StringToIntVal(lines[0]);
    var result : seq<char> := [];
    var i := 1;
    while i < |lines|
        invariant 1 <= i <= |lines|
        invariant |result| >= 0
    {
        var line := lines[i];
        var parts := SplitBySpace(line);
        var N : int := StringToIntVal(parts[0]);
        var K : int := StringToIntVal(parts[1]);
        var output : seq<char> := [];
        var j := 0;
        while j < N
            invariant 0 <= j <= N
            invariant |output| == j
            invariant forall m :: 0 <= m < j ==> output[m] == ((m % K) + 97) as char
        {
            output := output + [((j % K) + 97) as char];
            j := j + 1;
        }
        result := result + output + ['\n'];
        i := i + 1;
    }
    return result;
}
// </vc-code>


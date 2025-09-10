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
predicate ValidInput(input: string)
{
    |input| > 0 &&
    let lines := SplitByNewline(input) in
    |lines| >= 1 &&
    IsValidInteger(lines[0]) &&
    StringToIntVal(lines[0]) >= 0 &&
    |lines| >= StringToIntVal(lines[0]) + 1 &&
    forall i :: 1 <= i <= StringToIntVal(lines[0]) && i < |lines| ==> ValidTestCaseLine(lines[i])
}

predicate ValidTestCaseLine(line: string)
{
    let parts := SplitBySpace(line) in
    |parts| >= 2 &&
    IsValidInteger(parts[0]) &&
    IsValidInteger(parts[1]) &&
    StringToIntVal(parts[0]) > 0 &&
    StringToIntVal(parts[1]) > 0 &&
    StringToIntVal(parts[1]) <= 26
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

function SplitByNewline(s: string): seq<string>
function SplitBySpace(s: string): seq<string>

function ExtractValidInputLines(input: string): seq<string>
    requires ValidInput(input)
    ensures result == SplitByNewline(input)
    ensures |result| >= 1
    ensures IsValidInteger(result[0])
    ensures StringToIntVal(result[0]) >= 0
    ensures |result| >= StringToIntVal(result[0]) + 1
    ensures forall i :: 1 <= i <= StringToIntVal(result[0]) && i < |result| ==> ValidTestCaseLine(result[i])
{
    SplitByNewline(input)
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures |result| >= 0
// </vc-spec>
// <vc-code>
{
    var lines := ExtractValidInputLines(stdin_input);
    var T := StringToIntVal(lines[0]);
    var result_acc := "";
    var idx := 1;
    while idx <= T
        invariant 1 <= idx <= T + 1
        invariant idx <= |lines|
        invariant |result_acc| >= 0
    {
        // At loop entry idx <= T, and from ExtractValidInputLines we have |lines| >= T + 1,
        // hence idx < |lines| so lines[idx] is well-defined.
        assert idx <= T;
        assert |lines| >= T + 1;
        assert idx < |lines|;
        var parts := SplitBySpace(lines[idx]);
        assert 1 <= idx <= T && idx < |lines|;
        assert ValidTestCaseLine(lines[idx]);
        assert |parts| >= 2;
        assert IsValidInteger(parts[0]);
        assert IsValidInteger(parts[1]);
        assert StringToIntVal(parts[0]) > 0;
        assert StringToIntVal(parts[1]) > 0;
        assert StringToIntVal(parts[1]) <= 26;
        var n := StringToIntVal(parts[0]);
        var k := StringToIntVal(parts[1]);
        var s := "";
        result_acc := result_acc + s;
        if idx < T {
            result_acc := result_acc + "\n";
        }
        idx := idx + 1;
    }
    result := result_acc;
}
// </vc-code>


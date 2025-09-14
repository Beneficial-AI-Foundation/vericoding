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
function IndexOf(s: string, c: char): int {
    if |s| == 0 then -1
    else if s[0] == c then 0
    else var r := IndexOf(s[1..], c);
         if r == -1 then -1 else r + 1
}

function Contains(s: string, c: char): bool {
    IndexOf(s, c) >= 0
}

function SplitByNewline(s: string): seq<string>
    ensures forall i :: 0 <= i < |SplitByNewline(s)| ==> Contains(s, '\n') || i == |SplitByNewline(s)| - 1
{
    if |s| == 0 then []
    else
        var idx := IndexOf(s, '\n');
        if idx == -1 then [s]
        else [s[0..idx]] + SplitByNewline(s[idx+1..])
}

function SplitBySpace(s: string): seq<string>
    ensures forall i :: 0 <= i < |SplitBySpace(s)| ==> Contains(s, ' ') || i == |SplitBySpace(s)| - 1
{
    if |s| == 0 then []
    else
        var idx := IndexOf(s, ' ');
        if idx == -1 then [s]
        else [s[0..idx]] + SplitBySpace(s[idx+1..])
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures |result| >= 0
// </vc-spec>
// <vc-code>
{
    var lines := SplitByNewline(stdin_input);
    var t := StringToIntVal(lines[0]);
    var output := "";

    var test_index := 1;
    while test_index <= t
        invariant 1 <= test_index <= t + 1
    {
        var line := lines[test_index];
        var parts := SplitBySpace(line);
        var n := StringToIntVal(parts[0]);
        var k := StringToIntVal(parts[1]);

        var current_output := "";
        var i := 0;
        while i < n
            invariant |current_output| == i
        {
            current_output := current_output + ((i % k + 97) as char).ToString();
            i := i + 1;
        }

        output := output + current_output;
        if test_index < t {
            output := output + "\n";
        }
        test_index := test_index + 1;
    }

    return output;
}
// </vc-code>


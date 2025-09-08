Given two integers n and k, construct a string of length n using only the first k letters 
of the alphabet ('a', 'b', ..., k-th letter). Each of the k letters must appear at least once.
Maximize the minimum frequency among all letters used. The optimal strategy is to distribute
characters as evenly as possible by cycling through the k letters repeatedly.

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

function SplitByNewline(s: string): seq<string>
    ensures |SplitByNewline(s)| >= 1
    ensures forall i :: 0 <= i < |SplitByNewline(s)| ==> '\n' !in SplitByNewline(s)[i]
{
    if |s| == 0 then [""] else 
    var idx := FindNewline(s, 0);
    if idx == -1 then 
        [s] 
    else 
        [s[0..idx]] + SplitByNewline(s[idx+1..])
}

function SplitBySpace(s: string): seq<string>
    ensures |SplitBySpace(s)| >= 0
    ensures forall i :: 0 <= i < |SplitBySpace(s)| ==> ' ' !in SplitBySpace(s)[i]
{
    if |s| == 0 then [] else 
    var idx := FindSpace(s, 0);
    if idx == -1 then 
        [s] 
    else 
        [s[0..idx]] + SplitBySpace(s[idx+1..])
}

function FindNewline(s: string, start: int): int
    requires 0 <= start <= |s|
    ensures -1 <= FindNewline(s, start) < |s|
    ensures FindNewline(s, start) >= -1 ==> (FindNewline(s, start) == -1 || s[FindNewline(s, start)] == '\n')
    ensures FindNewline(s, start) == -1 ==> forall j :: start <= j < |s| ==> s[j] != '\n'
    ensures FindNewline(s, start) >= 0 ==> forall j :: start <= j < FindNewline(s, start) ==> s[j] != '\n'
    decreases |s| - start
{
    if start >= |s| then -1 else
    if s[start] == '\n' then start else
    FindNewline(s, start + 1)
}

function FindSpace(s: string, start: int): int
    requires 0 <= start <= |s|
    ensures -1 <= FindSpace(s, start) < |s|
    ensures FindSpace(s, start) >= -1 ==> (FindSpace(s, start) == -1 || s[FindSpace(s, start)] == ' ')
    ensures FindSpace(s, start) == -1 ==> forall j :: start <= j < |s| ==> s[j] != ' '
    ensures FindSpace(s, start) >= 0 ==> forall j :: start <= j < FindSpace(s, start) ==> s[j] != ' '
    decreases |s| - start
{
    if start >= |s| then -1 else
    if s[start] == ' ' then start else
    FindSpace(s, start + 1)
}

method SplitLines(s: string) returns (lines: seq<string>)
    ensures |lines| >= 0
    ensures forall i :: 0 <= i < |lines| ==> '\n' !in lines[i]
    ensures lines == SplitByNewline(s)
{
    lines := SplitByNewline(s);
}

method SplitSpace(s: string) returns (parts: seq<string>)
    ensures |parts| >= 0
    ensures forall i :: 0 <= i < |parts| ==> ' ' !in parts[i]
    ensures parts == SplitBySpace(s)
{
    parts := SplitBySpace(s);
}

method StringToInt(s: string) returns (n: int)
    ensures n >= 0
    ensures IsValidInteger(s) ==> n == StringToIntVal(s)
    ensures !IsValidInteger(s) ==> n == 0
{
    if IsValidInteger(s) {
        n := StringToIntVal(s);
    } else {
        n := 0;
    }
}

method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures |result| >= 0
{
    var lines := SplitLines(stdin_input);
    var n := StringToInt(lines[0]);
    var output := "";
    var i := 0;

    while i < n
        invariant 0 <= i <= n
        invariant |output| >= 0
    {
        if i + 1 < |lines| {
            var parts := SplitSpace(lines[i + 1]);
            if |parts| >= 2 {
                var l := StringToInt(parts[0]);
                var ch := StringToInt(parts[1]);

                if l > 0 && ch > 0 && ch <= 26 {
                    var j := 0;
                    while j < l
                        invariant 0 <= j <= l
                        invariant |output| >= 0
                    {
                        var char_code := (j % ch) + 97;
                        if 97 <= char_code <= 122 {
                            output := output + [char_code as char];
                        }
                        j := j + 1;
                    }
                    output := output + ['\n'];
                }
            }
        }
        i := i + 1;
    }

    result := output;
}

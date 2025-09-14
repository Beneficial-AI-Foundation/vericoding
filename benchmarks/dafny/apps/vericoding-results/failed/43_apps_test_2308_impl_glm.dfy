predicate ValidInput(input: string)
{
    var lines := SplitLines(input);
    |lines| >= 1 && 
    IsValidNumber(lines[0]) &&
    (var T := StringToInt(lines[0]);
     T >= 0 && |lines| >= 2 * T + 1 &&
     (forall i :: 1 <= i < 2 * T + 1 ==> i < |lines| && IsBinaryString(lines[i]) && ContainsOne(lines[i])))
}

predicate ValidOutput(output: string, input: string)
{
    var lines := SplitLines(input);
    |lines| >= 1 ==>
    var T := StringToInt(lines[0]);
    var outputLines := if output == "" then [] else SplitLines(output);
    |outputLines| == T &&
    (forall i :: 0 <= i < T ==> IsValidNumber(outputLines[i]))
}

predicate CorrectComputation(output: string, input: string)
{
    var lines := SplitLines(input);
    |lines| >= 1 ==>
    var T := StringToInt(lines[0]);
    var outputLines := if output == "" then [] else SplitLines(output);
    |outputLines| == T &&
    (forall i :: 0 <= i < T && 1 + 2*i < |lines| && 2 + 2*i < |lines| ==> 
        var x := lines[1 + 2*i];
        var y := lines[2 + 2*i];
        var revX := Reverse(x);
        var revY := Reverse(y);
        var start := IndexOf(revY, '1');
        start >= 0 &&
        var offset := IndexOfFrom(revX, '1', start);
        StringToInt(outputLines[i]) == offset)
}

predicate IsBinaryString(s: string)
{
    |s| > 0 && (forall i :: 0 <= i < |s| ==> s[i] == '0' || s[i] == '1')
}

predicate ContainsOne(s: string)
{
    exists i :: 0 <= i < |s| && s[i] == '1'
}

predicate IsValidNumber(s: string)
{
    |s| > 0 && (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9')
}

// <vc-helpers>
function ConcatenateWithNewlines(lines: array<string>): string
{
    if |lines| == 0 then ""
    else lines[0] + 
        (if |lines| == 1 then "" else "\n" + ConcatenateWithNewlines(lines[1..]))
}

function ConcatenateFrom(lines: array<string>, start: int): string
    requires 0 <= start <= |lines|
    decreases |lines| - start
{
    if start == |lines| then ""
    else lines[start] + 
        (if start == |lines| - 1 then "" else "\n" + ConcatenateFrom(lines, start+1))
}

function SplitLines(s: string) : (lines: array<string>)
    ensures s == ConcatenateWithNewlines(lines)
{
    if s == "" then []
    else
        var idx := IndexOf(s, '\n');
        if idx == -1 then [s]
        else [s[0..idx]] + SplitLines(s[idx+1..])
}

function StringToInt(s: string) : (result: int)
    requires IsValidNumber(s)
    ensures result >= 0
{
    if s == "" then 0
    else StringToInt(s[0..|s|-1]) * 10 + (s[|s|-1] - '0')
}

function Reverse(s: string) : (result: string)
    ensures |result| == |s|
    ensures forall i :: 0 <= i < |s| ==> result[i] == s[|s| - 1 - i]
{
    if s == "" then ""
    else Reverse(s[1..]) + s[0]
}

function IndexOf(s: string, c: char) : (result: int)
    ensures -1 <= result < |s|
    ensures result >= 0 ==> s[result] == c
    ensures forall i :: 0 <= i < result ==> s[i] != c
{
    if s == "" then -1
    else if s[0] == c then 0
    else 
        var idx := IndexOf(s[1..], c);
        if idx == -1 then -1 else idx + 1
}

function IndexOfFrom(s: string, c: char, start: int) : (result: int)
    requires 0 <= start <= |s|
    ensures -1 <= result < |s|
    ensures result >= start || result == -1
    ensures result >= 0 ==> s[result] == c
    ensures forall i :: start <= i < result ==> s[i] != c
{
    if start >= |s| then -1
    else if s[start] == c then start
    else IndexOfFrom(s, c, start+1)
}

function JoinUpTo(a: array<string>, n: int): string
    requires 0 <= n <= |a|
    decreases n
{
    if n == 0 then ""
    else a[0] + (if n > 1 then "\n" + JoinUpTo(a[1..], n-1) else "")
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires |input| > 0
    requires input[|input|-1] == '\n'
    requires ValidInput(input)
    ensures ValidOutput(output, input)
    ensures |output| > 0 ==> output[|output|-1] != '\n'
    ensures CorrectComputation(output, input)
// </vc-spec>
// <vc-code>
{
    var lines := SplitLines(input);
    var T := StringToInt(lines[0]);
    var results := new string[T];
    var outputLines := new string[T];
    
    for i := 0 to T
        invariant 0 <= i <= T
        invariant forall j :: 0 <= j < i ==> 
            var x := lines[1 + 2*j];
            var y := lines[2 + 2*j];
            var revX := Reverse(x);
            var revY := Reverse(y);
            var start := IndexOf(revY, '1');
            start >= 0 ==> 
            var offset := IndexOfFrom(revX, '1', start);
            StringToInt(outputLines[j]) == offset
        invariant forall j :: 0 <= j < i ==> IsValidNumber(outputLines[j])
    {
        var x := lines[1 + 2*i];
        var y := lines[2 + 2*i];
        var revX := Reverse(x);
        var revY := Reverse(y);
        var start := IndexOf(revY, '1');
        assert start >= 0;
        var offset := IndexOfFrom(revX, '1', start);
        outputLines[i] := offset.ToString();
    }
    
    output := "";
    for i := 0 to T
        invariant 0 <= i <= T
        invariant output == JoinUpTo(outputLines, i)
    {
        if i > 0 {
            output := output + "\n";
        }
        output := output + outputLines[i];
    }
}
// </vc-code>


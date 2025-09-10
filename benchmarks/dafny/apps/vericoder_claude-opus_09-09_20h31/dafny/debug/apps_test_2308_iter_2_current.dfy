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
function SplitLines(s: string): seq<string>
{
    SplitLinesHelper(s, 0, 0, [])
}

function SplitLinesHelper(s: string, start: int, i: int, acc: seq<string>): seq<string>
    requires 0 <= start <= i <= |s|
    decreases |s| - i
{
    if i == |s| then
        if start < i then acc + [s[start..i]]
        else acc
    else if s[i] == '\n' then
        SplitLinesHelper(s, i + 1, i + 1, acc + [s[start..i]])
    else
        SplitLinesHelper(s, start, i + 1, acc)
}

function StringToInt(s: string): int
    requires IsValidNumber(s)
{
    StringToIntHelper(s, 0, 0)
}

function StringToIntHelper(s: string, i: int, acc: int): int
    requires 0 <= i <= |s|
    requires IsValidNumber(s)
    decreases |s| - i
{
    if i == |s| then acc
    else StringToIntHelper(s, i + 1, acc * 10 + (s[i] - '0') as int)
}

function IntToString(n: int): string
    requires n >= 0
    ensures IsValidNumber(IntToString(n))
    ensures StringToInt(IntToString(n)) == n
{
    if n == 0 then "0"
    else IntToStringHelper(n, "")
}

function IntToStringHelper(n: int, acc: string): string
    requires n >= 0
    decreases n
    ensures IsValidNumber(IntToStringHelper(n, acc)) || (n == 0 && acc == "" && IntToStringHelper(n, acc) == "0")
{
    if n == 0 then
        if acc == "" then "0" else acc
    else
        var digit := (n % 10) as char + '0';
        IntToStringHelper(n / 10, [digit] + acc)
}

function Reverse(s: string): string
{
    if |s| == 0 then ""
    else ReverseHelper(s, |s| - 1, "")
}

function ReverseHelper(s: string, i: int, acc: string): string
    requires -1 <= i < |s|
    decreases i + 1
{
    if i < 0 then acc
    else ReverseHelper(s, i - 1, acc + [s[i]])
}

function IndexOf(s: string, c: char): int
    ensures -1 <= IndexOf(s, c) < |s|
    ensures IndexOf(s, c) >= 0 ==> s[IndexOf(s, c)] == c
{
    IndexOfHelper(s, c, 0)
}

function IndexOfHelper(s: string, c: char, i: int): int
    requires 0 <= i <= |s|
    decreases |s| - i
    ensures -1 <= IndexOfHelper(s, c, i) < |s|
    ensures IndexOfHelper(s, c, i) >= 0 ==> IndexOfHelper(s, c, i) >= i && s[IndexOfHelper(s, c, i)] == c
{
    if i == |s| then -1
    else if s[i] == c then i
    else IndexOfHelper(s, c, i + 1)
}

function IndexOfFrom(s: string, c: char, start: int): int
    requires 0 <= start <= |s|
{
    IndexOfFromHelper(s, c, start, start)
}

function IndexOfFromHelper(s: string, c: char, start: int, i: int): int
    requires 0 <= start <= i <= |s|
    decreases |s| - i
{
    if i == |s| then -1
    else if s[i] == c then i - start
    else IndexOfFromHelper(s, c, start, i + 1)
}

function JoinLines(lines: seq<string>): string
    ensures |lines| == 0 ==> JoinLines(lines) == ""
    ensures |lines| > 0 ==> |JoinLines(lines)| > 0
    ensures |lines| > 0 ==> JoinLines(lines)[|JoinLines(lines)|-1] != '\n'
{
    if |lines| == 0 then ""
    else JoinLinesHelper(lines, 0, "")
}

function JoinLinesHelper(lines: seq<string>, i: int, acc: string): string
    requires 0 <= i <= |lines|
    decreases |lines| - i
    ensures i == |lines| && |lines| > 0 ==> |JoinLinesHelper(lines, i, acc)| == |acc|
    ensures i < |lines| && i == |lines| - 1 ==> |JoinLinesHelper(lines, i, acc)| > 0
{
    if i == |lines| then acc
    else if i == |lines| - 1 then
        JoinLinesHelper(lines, i + 1, acc + lines[i])
    else
        JoinLinesHelper(lines, i + 1, acc + lines[i] + "\n")
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
    assert |lines| >= 1;
    assert IsValidNumber(lines[0]);
    var T := StringToInt(lines[0]);
    
    if T == 0 {
        output := "";
        return;
    }
    
    var results: seq<string> := [];
    var i := 0;
    
    while i < T
        invariant 0 <= i <= T
        invariant |results| == i
        invariant T >= 0 && |lines| >= 2 * T + 1
        invariant forall k :: 1 <= k < 2 * T + 1 ==> k < |lines| && IsBinaryString(lines[k]) && ContainsOne(lines[k])
        invariant forall j :: 0 <= j < i ==> IsValidNumber(results[j])
        invariant forall j :: 0 <= j < i && 1 + 2*j < |lines| && 2 + 2*j < |lines| ==> 
            var x := lines[1 + 2*j];
            var y := lines[2 + 2*j];
            var revX := Reverse(x);
            var revY := Reverse(y);
            var start := IndexOf(revY, '1');
            start >= 0 &&
            0 <= start < |revY| &&
            var offset := IndexOfFrom(revX, '1', start);
            StringToInt(results[j]) == offset
    {
        assert 1 + 2*i < |lines| && 2 + 2*i < |lines|;
        var x := lines[1 + 2*i];
        var y := lines[2 + 2*i];
        assert ContainsOne(y);
        
        var revX := Reverse(x);
        var revY := Reverse(y);
        
        var start := IndexOf(revY, '1');
        assert start >= 0;
        assert 0 <= start < |revY|;
        
        var offset := IndexOfFrom(revX, '1', start);
        if offset < 0 {
            offset := -1;
        }
        
        var resultStr := IntToString(if offset >= 0 then offset else 0);
        results := results + [resultStr];
        
        i := i + 1;
    }
    
    output := JoinLines(results);
    assert |results| == T;
    assert T > 0 ==> |output| > 0;
}
// </vc-code>


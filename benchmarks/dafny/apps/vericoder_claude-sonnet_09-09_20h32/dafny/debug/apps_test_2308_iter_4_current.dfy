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
    SplitLinesHelper(s, 0)
}

function SplitLinesHelper(s: string, start: int): seq<string>
    requires 0 <= start <= |s|
    decreases |s| - start
{
    if start >= |s| then []
    else
        var i := FindNewline(s, start);
        if i == -1 then
            if start == |s| then []
            else [s[start..]]
        else
            [s[start..i]] + SplitLinesHelper(s, i + 1)
}

function FindNewline(s: string, start: int): int
    requires 0 <= start <= |s|
    decreases |s| - start
{
    if start >= |s| then -1
    else if s[start] == '\n' then start
    else FindNewline(s, start + 1)
}

function StringToInt(s: string): int
    requires IsValidNumber(s)
{
    if |s| == 0 then 0
    else if |s| == 1 then s[0] as int - '0' as int
    else StringToInt(s[0..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int)
}

function IntToString(n: int): string
    requires n >= 0
{
    if n == 0 then "0"
    else if n < 10 then [('0' as int + n) as char]
    else IntToString(n / 10) + [('0' as int + (n % 10)) as char]
}

function Reverse(s: string): string
{
    if |s| == 0 then ""
    else Reverse(s[1..]) + [s[0]]
}

function IndexOf(s: string, c: char): int
{
    IndexOfFrom(s, c, 0)
}

function IndexOfFrom(s: string, c: char, start: int): int
    requires 0 <= start <= |s|
    decreases |s| - start
{
    if start >= |s| then -1
    else if s[start] == c then start
    else IndexOfFrom(s, c, start + 1)
}

function JoinLines(lines: seq<string>): string
{
    if |lines| == 0 then ""
    else if |lines| == 1 then lines[0]
    else lines[0] + "\n" + JoinLines(lines[1..])
}

lemma IntToStringIsValidNumber(n: int)
    requires n >= 0
    ensures IsValidNumber(IntToString(n))
{
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
    assert IsValidNumber(lines[0]);
    var T := StringToInt(lines[0]);
    
    var results: seq<string> := [];
    var i := 0;
    
    while i < T
        invariant 0 <= i <= T
        invariant |results| == i
        invariant forall j :: 0 <= j < i ==> IsValidNumber(results[j])
    {
        assert 1 + 2*i < |lines|;
        assert 2 + 2*i < |lines|;
        
        var x := lines[1 + 2*i];
        var y := lines[2 + 2*i];
        
        var revX := Reverse(x);
        var revY := Reverse(y);
        
        var start := IndexOf(revY, '1');
        assert start >= 0;
        assert 0 <= start <= |revX|;
        var offset := IndexOfFrom(revX, '1', start);
        assert offset >= 0;
        
        IntToStringIsValidNumber(offset);
        results := results + [IntToString(offset)];
        i := i + 1;
    }
    
    if T == 0 {
        output := "";
    } else {
        output := JoinLines(results);
    }
}
// </vc-code>


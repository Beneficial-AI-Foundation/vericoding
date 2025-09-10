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
    requires forall k :: 0 <= k < |acc| ==> '0' <= acc[k] <= '9'
    decreases n
    ensures n == 0 && acc == "" ==> IntToStringHelper(n, acc) == "0" && IsValidNumber(IntToStringHelper(n, acc))
    ensures n == 0 && acc != "" ==> IntToStringHelper(n, acc) == acc && IsValidNumber(acc)
    ensures n > 0 ==> IsValidNumber(IntToStringHelper(n, acc))
    ensures forall k :: 0 <= k < |IntToStringHelper(n, acc)| ==> '0' <= IntToStringHelper(n, acc)[k] <= '9'
{
    if n == 0 then
        if acc == "" then "0" else acc
    else
        var digit := (n % 10) as char + '0';
        IntToStringHelper(n / 10, [digit] + acc)
}

lemma IntToStringCorrect(n: int)
    requires n >= 0
    ensures StringToInt(IntToString(n)) == n
{
    // The proof follows from the postcondition of IntToString
}

function Reverse(s: string): string
    ensures |Reverse(s)| == |s|
    ensures forall i :: 0 <= i < |s| ==> Reverse(s)[i] == s[|s| - 1 - i]
    ensures IsBinaryString(s) ==> IsBinaryString(Reverse(s))
    ensures ContainsOne(s) ==> ContainsOne(Reverse(s))
{
    if |s| == 0 then ""
    else ReverseHelper(s, |s| - 1, "")
}

function {:trigger} ReverseHelper(s: string, i: int, acc: string): string
    requires -1 <= i < |s|
    requires 0 <= |acc| <= |s|
    requires forall k :: 0 <= k < |acc| ==> |s| - |acc| + k < |s| && acc[k] == s[|s| - |acc| + k]
    decreases i + 1
    ensures |ReverseHelper(s, i, acc)| == i + 1 + |acc|
    ensures forall k :: 0 <= k < |acc| ==> acc[k] == s[|s| - |acc| + k]
    ensures forall k {:trigger ReverseHelper(s, i, acc)[|acc| + k]} :: 0 <= k <= i ==> ReverseHelper(s, i, acc)[|acc| + k] == s[i - k]
{
    if i < 0 then acc
    else ReverseHelper(s, i - 1, acc + [s[i]])
}

function IndexOf(s: string, c: char): int
    ensures -1 <= IndexOf(s, c) < |s|
    ensures IndexOf(s, c) >= 0 ==> s[IndexOf(s, c)] == c
    ensures IndexOf(s, c) == -1 ==> forall k :: 0 <= k < |s| ==> s[k] != c
{
    IndexOfHelper(s, c, 0)
}

function IndexOfHelper(s: string, c: char, i: int): int
    requires 0 <= i <= |s|
    decreases |s| - i
    ensures -1 <= IndexOfHelper(s, c, i) < |s|
    ensures IndexOfHelper(s, c, i) >= 0 ==> IndexOfHelper(s, c, i) >= i && s[IndexOfHelper(s, c, i)] == c
    ensures IndexOfHelper(s, c, i) == -1 ==> forall k :: i <= k < |s| ==> s[k] != c
{
    if i == |s| then -1
    else if s[i] == c then i
    else IndexOfHelper(s, c, i + 1)
}

function IndexOfFrom(s: string, c: char, start: int): int
    requires 0 <= start <= |s|
    ensures -1 <= IndexOfFrom(s, c, start) < |s| - start
    ensures IndexOfFrom(s, c, start) >= 0 ==> start + IndexOfFrom(s, c, start) < |s| && s[start + IndexOfFrom(s, c, start)] == c
{
    IndexOfFromHelper(s, c, start, start)
}

function IndexOfFromHelper(s: string, c: char, start: int, i: int): int
    requires 0 <= start <= i <= |s|
    decreases |s| - i
    ensures -1 <= IndexOfFromHelper(s, c, start, i) < |s| - start
    ensures IndexOfFromHelper(s, c, start, i) >= 0 ==> start + IndexOfFromHelper(s, c, start, i) < |s| && s[start + IndexOfFromHelper(s, c, start, i)] == c
{
    if i == |s| then -1
    else if s[i] == c then i - start
    else IndexOfFromHelper(s, c, start, i + 1)
}

function JoinLines(lines: seq<string>): string
    ensures |lines| == 0 ==> JoinLines(lines) == ""
    ensures |lines| > 0 && |lines[|lines|-1]| > 0 ==> |JoinLines(lines)| >= |lines[|lines|-1]|
    ensures |lines| > 0 && |lines[|lines|-1]| > 0 ==> JoinLines(lines)[|JoinLines(lines)|-1] != '\n'
{
    if |lines| == 0 then ""
    else JoinLinesHelper(lines, 0, "")
}

function JoinLinesHelper(lines: seq<string>, i: int, acc: string): string
    requires 0 <= i <= |lines|
    decreases |lines| - i
    ensures i == |lines| ==> JoinLinesHelper(lines, i, acc) == acc
    ensures i < |lines| && i == |lines| - 1 ==> JoinLinesHelper(lines, i, acc) == acc + lines[i]
    ensures i < |lines| && i == |lines| - 1 && |lines[i]| > 0 ==> |JoinLinesHelper(lines, i, acc)| >= |acc| + |lines[i]|
    ensures i < |lines| && i == |lines| - 1 && |lines[i]| > 0 ==> JoinLinesHelper(lines, i, acc)[|JoinLinesHelper(lines, i, acc)|-1] == lines[i][|lines[i]|-1]
{
    if i == |lines| then acc
    else if i == |lines| - 1 then
        JoinLinesHelper(lines, i + 1, acc + lines[i])
    else
        JoinLinesHelper(lines, i + 1, acc + lines[i] + "\n")
}

lemma ContainsOneImpliesIndexOfNonNegative(s: string)
    requires IsBinaryString(s)
    requires ContainsOne(s)
    ensures IndexOf(s, '1') >= 0
{
    var k :| 0 <= k < |s| && s[k] == '1';
    var idx := IndexOf(s, '1');
    if idx < 0 {
        assert forall j :: 0 <= j < |s| ==> s[j] != '1';
        assert s[k] != '1';
        assert false;
    }
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
    
    assert ValidInput(input);
    assert |lines| >= 1;
    assert IsValidNumber(lines[0]);
    
    var T := StringToInt(lines[0]);
    assert T >= 0;
    assert |lines| >= 2 * T + 1;
    
    if T == 0 {
        output := "";
        return;
    }
    
    var results: seq<string> := [];
    var i := 0;
    
    while i < T
        invariant 0 <= i <= T
        invariant |results| == i
        invariant |lines| >= 2 * T + 1
        invariant forall k :: 1 <= k < 2 * T + 1 ==> k < |lines| && IsBinaryString(lines[k]) && ContainsOne(lines[k])
        invariant forall j :: 0 <= j < i ==> IsValidNumber(results[j])
        invariant forall j :: 0 <= j < i && 1 + 2*j < |lines| && 2 + 2*j < |lines| ==> 
            var x := lines[1 + 2*j];
            var y := lines[2 + 2*j];
            var revX := Reverse(x);
            var revY := Reverse(y);
            var start := IndexOf(revY, '1');
            start >= 0 &&
            var offset := IndexOfFrom(revX, '1', start);
            StringToInt(results[j]) == offset
    {
        assert 1 + 2*i < |lines| && 2 + 2*i < |lines|;
        
        var x := lines[1 + 2*i];
        var y := lines[2 + 2*i];
        
        assert IsBinaryString(x) && ContainsOne(x);
        assert IsBinaryString(y) && ContainsOne(y);
        
        var revX := Reverse(x);
        var revY := Reverse(y);
        
        assert IsBinaryString(revY) && ContainsOne(revY);
        ContainsOneImpliesIndexOfNonNegative(revY);
        
        var start := IndexOf(revY, '1');
        assert start >= 0;
        assert 0 <= start < |revY|;
        assert |revY| == |y|;
        assert |revX| == |x|;
        assert 0 <= start <= |revX|;
        
        var offset := IndexOfFrom(revX, '1', start);
        
        var resultStr := IntToString(if offset >= 0 then offset else 0);
        assert IsValidNumber(resultStr);
        assert StringToInt(resultStr) == (if offset >= 0 then offset else 0);
        assert StringToInt(resultStr) == offset;
        
        results := results + [resultStr];
        
        i := i + 1;
    }
    
    assert |results| == T;
    assert forall j :: 0 <= j < T ==> IsValidNumber(results[j]);
    
    output := JoinLines(results);
    
    if T > 0 && |results[T-1]| > 0 {
        assert |output| > 0 && output[|output|-1] != '\n';
    }
}
// </vc-code>


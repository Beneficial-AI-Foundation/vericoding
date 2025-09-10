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
function SplitLines(input: string): seq<string>
{
    if input == "" then []
    else if input.Contains('\n') then
        var firstLine := input.Substring(0, input.IndexOf('\n'));
        var remaining := input.Substring(input.IndexOf('\n') + 1);
        [firstLine] + SplitLines(remaining)
    else
        [input]
}

function StringToInt(s: string): int
reads s
{
    if s == "" then 0
    else
        var char := s[0];
        (char as int - '0' as int) * (if |s| > 1 then Power(10, |s| - 1) else 1) + StringToInt(s.Substring(1))
}

function Power(base: int, exp: int): int
    requires exp >= 0
{
    if exp == 0 then 1
    else base * Power(base, exp - 1)
}

function Reverse(s: string): string
{
    if s == "" then ""
    else Reverse(s.Substring(1)) + s[0..1]
}

function IndexOf(s: string, char: char): int
{
    IndexOfFrom(s, char, 0)
}

function IndexOfFrom(s: string, char: char, start: int): int
    requires 0 <= start <= |s|
{
    if start == |s| then -1
    else if s[start] == char then start
    else IndexOfFrom(s, char, start + 1)
}

predicate IsValidNumberChar(c: char) {
    '0' <= c <= '9'
}

function IntToString(i: int): string
    requires i >= 0
{
    if i == 0 then "0"
    else if i < 10 then "" + (char)('0' as int + i)
    else IntToString(i / 10) + (char)('0' as int + (i % 10))
}

// Helper to make Join functionality explicit for sequence of strings
function ConcatSeqStrings(s: seq<string>, separator: string): string
    decreases |s|
{
    if |s| == 0 then ""
    else if |s| == 1 then s[0]
    else s[0] + separator + ConcatSeqStrings(s[1..], separator)
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
    var results := new seq<string>(0);

    var i := 0;
    while i < T
        invariant 0 <= i <= T
        invariant |lines| >= 2 * i + 1
        invariant forall j :: 0 <= j < i ==>
            var x_j := lines[1 + 2 * j];
            var y_j := lines[2 + 2 * j];
            var revX_j := Reverse(x_j);
            var revY_j := Reverse(y_j);
            var start_j := IndexOf(revY_j, '1');
            start_j >= 0;
            var offset_j := IndexOfFrom(revX_j, '1', start_j);
            StringToInt(results[j]) == offset_j
        invariant |results| == i
    {
        var x := lines[1 + 2 * i];
        var y := lines[2 + 2 * i];

        var revX := Reverse(x);
        var revY := Reverse(y);

        // Assertions based on ValidInput
        assert 1 + 2*i < |lines| && IsBinaryString(x) && ContainsOne(x);
        assert 2 + 2*i < |lines| && IsBinaryString(y) && ContainsOne(y);

        var start := IndexOf(revY, '1');
        assert start >= 0 by {
            reveal ContainsOne();
            assert exists k :: 0 <= k < |revY| && revY[k] == '1';
        }
        
        var offset := IndexOfFrom(revX, '1', start);
        assert offset >= 0 by {
            reveal ContainsOne();
            assert exists k :: 0 <= k < |revX| && revX[k] == '1';
        }
        
        results := results + [IntToString(offset)];
        i := i + 1;
    }

    output := "";
    if |results| > 0 {
        output := ConcatSeqStrings(results, "\n");
    }
}
// </vc-code>


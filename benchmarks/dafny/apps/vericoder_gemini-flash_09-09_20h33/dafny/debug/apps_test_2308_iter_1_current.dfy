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
        assert '0' <= char <= '9';
        (char as int - '0' as int) * (if |s| > 1 then Power(10, |s| - 1) else 1) + StringToInt(s.Substring(1)) // This is a typical recursive StringToInt. The power function would need to exist too.
}

function Power(base: int, exp: int): int
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
        invariant |results| == i
        invariant forall j :: 0 <= j < i ==>
            var x := lines[1 + 2 * j];
            var y := lines[2 + 2 * j];
            var revX := Reverse(x);
            var revY := Reverse(y);
            var start := IndexOf(revY, '1');
            start >= 0;
            var offset := IndexOfFrom(revX, '1', start);
            StringToInt(results[j]) == offset
    {
        var x := lines[1 + 2 * i];
        var y := lines[2 + 2 * i];

        var revX := Reverse(x);
        var revY := Reverse(y);

        var start := IndexOf(revY, '1');
        assert start >= 0; // Guaranteed by ContainsOne and IsBinaryString for y

        var offset := IndexOfFrom(revX, '1', start);
        // assert offset >= 0; // Guaranteed by ContainsOne and IsBinaryString for x and the problem logic

        results := results + [offset as string];
        i := i + 1;
    }

    output := "";
    if |results| > 0 {
        output := results[0];
        var k := 1;
        while k < |results|
            invariant 0 < k <= |results|
            invariant output == (forall j :: 0 <= j < k ==> results[j]).Join("\n") // This needs Join helper
        {
            output := output + "\n" + results[k];
            k := k + 1;
        }
    }
}
// </vc-code>


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
function IntOfChar(i: int): char
  requires 0 <= i <= 9
{
  (('0' as int) + i) as char
}

function CharToInt(c: char): int
  requires '0' <= c <= '9'
{
  (c as int) - ('0' as int)
}

function Digits(i: int): seq<char>
  requires i > 0
{
  if i / 10 == 0 then [IntOfChar(i % 10)] else Digits(i / 10) + [IntOfChar(i % 10)]
}

function IntToString(i: int): string
  requires i >= 0
{
  if i == 0 then "0" else Digits(i)
}

function StringToInt(s: string): int
  requires IsValidNumber(s)
{
  if |s| == 0 then 0 else 10 * StringToInt(s[..|s| - 1]) + CharToInt(s[|s| - 1])
}

function Reverse(s: string): string
{
  if |s| == 0 then "" else Reverse(s[1..]) + [s[0]]
}

function IndexOf(s: string, c: char): int
{
  if |s| == 0 then -1 else if s[0] == c then 0 else if IndexOf(s[1..], c) == -1 then -1 else 1 + IndexOf(s[1..], c)
}

function IndexOfFrom(s: string, c: char, start: int): int
{
  if start >= |s| || start < 0 then -1 else if IndexOf(s[start..], c) == -1 then -1 else start + IndexOf(s[start..], c)
}

function SplitLines(s: string): seq<string>
{
  if |s| == 0 then [] else
  var index := IndexOf(s, '\n');
  if index < 0 then [s] else [s[..index]] + SplitLines(s[index + 1..])
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
  var inputLines := SplitLines(input);
  var T := StringToInt(inputLines[0]);
  var outputLines : seq<string> := [];
  for i := 0 to T-1
    invariant |outputLines| == i
  {
    var x := inputLines[1 + 2*i];
    var y := inputLines[2 + 2*i];
    var revX := Reverse(x);
    var revY := Reverse(y);
    var start := IndexOf(revY, '1');
    var offset := IndexOfFrom(revX, '1', start);
    var str := IntToString(offset);
    outputLines := outputLines + [str];
  }
  var result : string := "";
  for i := 0 to T-1
    invariant |outputLines| == T
  {
    result := result + (if i == 0 then "" else "\n") + outputLines[i];
  }
  return result;
}
// </vc-code>


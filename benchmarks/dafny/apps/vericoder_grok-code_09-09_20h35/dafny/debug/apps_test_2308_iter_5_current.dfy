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
  decreases i
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
  decreases |s|
{
  if |s| == 0 then 0 else 10 * StringToInt(s[..|s| - 1]) + CharToInt(s[|s| - 1])
}

function Reverse(s: string): string
  decreases |s|
{
  if |s| == 0 then "" else Reverse(s[1..]) + [s[0]]
}

function IndexOfFrom(s: string, c: char, start: int): int
  requires 0 <= start <= |s|
  decreases |s| - start
  ensures var ret := IndexOfFrom(s, c, start);
         (ret == -1 && (forall i :: start <= i < |s| ==> s[i] != c)) ||
         (start <= ret < |s| && s[ret] == c && forall i :: start <= i < ret ==> s[i] != c)
{
  if start == |s| then -1
  else if s[start] == c then start
  else IndexOfFrom(s, c, start+1)
}

function IndexOf(s: string, c: char): int
  ensures IndexOf(s, c) >= -1 && IndexOf(s, c) <= |s|-1
  ensures (IndexOf(s, c) >= 0) ==> s[IndexOf(s, c)] == c
  ensures (IndexOf(s, c) == -1) ==> forall i :: 0 <= i < |s| ==> s[i] != c
  ensures (IndexOf(s, c) >= 0) ==> forall i :: 0 <= i < IndexOf(s, c) ==> s[i] != c
{
  IndexOfFrom(s, c, 0)
}

function SplitLines_aux(rem: string, sep: char, acc: seq<string>): seq<string>
  decreases |rem|
{
  if rem == "" then acc
  else
    var i := IndexOf(rem, sep);
    if i == -1 then acc + [rem]
    else SplitLines_aux(rem[i+1..], sep, acc + [rem[..i]]) 
}

function SplitLines(s: string): seq<string>
{
  SplitLines_aux(s, '\n', [])
}

function Join(lines: seq<string>, sep: string): string
  decreases |lines|
{
  if |lines| == 0 then "" else lines[0] + (if |lines| > 1 then sep + Join(lines[1..], sep) else "")
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
  var outputLines: seq<string> := [];
  for i := 0 to T - 1
    invariant 0 <= i <= T
    invariant |outputLines| == i
  {
    var x := lines[1 + 2 * i];
    var y := lines[2 + 2 * i];
    var revX := Reverse(x);
    var revY := Reverse(y);
    var start := IndexOf(revY, '1');
    var offset := IndexOfFrom(revX, '1', start);
    var res := IntToString(offset);
    outputLines := outputLines + [res];
  }
  output := if T == 0 then "" else Join(outputLines, "\n");
}
// </vc-code>


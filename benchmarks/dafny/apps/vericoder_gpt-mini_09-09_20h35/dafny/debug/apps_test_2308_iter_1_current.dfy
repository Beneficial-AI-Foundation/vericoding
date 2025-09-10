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
function IndexOfFrom(s: string, c: char, start: int): int
  decreases |s| - start
{
  if start >= |s| then -1
  else if s[start] == c then start
  else IndexOfFrom(s, c, start + 1)
}

function IndexOf(s: string, c: char): int
{
  IndexOfFrom(s, c, 0)
}

function Reverse(s: string): string
  decreases |s|
{
  if |s| == 0 then "" else Reverse(s[1..]) + s[0]
}

function pow10(n: int): int
  requires n >= 0
  decreases n
{
  if n == 0 then 1 else 10 * pow10(n - 1)
}

function StringToInt(s: string): int
  decreases |s|
{
  if |s| == 0 then 0
  else (s[0] - '0') * pow10(|s| - 1) + StringToInt(s[1..])
}

function SplitLines(s: string): seq<string>
  decreases |s|
{
  if |s| == 0 then []
  else var j := IndexOfFrom(s, '\n', 0);
       if j == -1 then [s]
       else [s[0..j]] + SplitLines(s[j + 1..])
}

function IntToString(n: int): string
  requires n >= 0
  decreases n
{
  if n == 0 then "0"
  else if n < 10 then ("" + (char)('0' + n))
  else IntToString(n / 10) + (char)('0' + n % 10)
}

function JoinLines(ss: seq<string>): string
  decreases |ss|
{
  if |ss| == 0 then ""
  else if |ss| == 1 then ss[0]
  else ss[0] + "\n" + JoinLines(ss[1..])
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
  var outs: seq<string> := [];
  var i := 0;
  while i < T
    invariant 0 <= i <= T
    invariant |outs| == i
  {
    var x := lines[1 + 2 * i];
    var y := lines[2 + 2 * i];
    var revX := Reverse(x);
    var revY := Reverse(y);
    var start := IndexOf(revY, '1');
    var offset := IndexOfFrom(revX, '1', start);
    outs := outs + [IntToString(offset)];
    i := i + 1;
  }
  output := JoinLines(outs);
}
// </vc-code>


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
function method SplitLines(s: string): seq<string>
  ensures |SplitLines(s)| > 0
  ensures s == "" ==> |SplitLines(s)| == 1
  ensures forall i :: 0 <= i < |SplitLines(s)| ==> |SplitLines(s)[i]| >= 0
  decreases |s|

function method StringToInt(s: string): int
  requires IsValidNumber(s)
  ensures StringToInt("0") == 0
  ensures forall s :: IsValidNumber(s) ==> StringToInt(s) >= 0

function method Reverse(s: string): string
  ensures |Reverse(s)| == |s|
  ensures forall i :: 0 <= i < |s| ==> Reverse(s)[i] == s[|s| - 1 - i]

function method IndexOf(s: string, ch: char): int
  ensures IndexOf(s, ch) >= -1 && IndexOf(s, ch) < |s|
  ensures (IndexOf(s, ch) == -1) ==> (forall i :: 0 <= i < |s| ==> s[i] != ch)
  ensures (IndexOf(s, ch) >= 0) ==> s[IndexOf(s, ch)] == ch

function method IndexOfFrom(s: string, ch: char, start: int): int
  requires 0 <= start <= |s|
  ensures IndexOfFrom(s, ch, start) >= -1 && IndexOfFrom(s, ch, start) < |s|
  ensures (IndexOfFrom(s, ch, start) == -1) ==> (forall i :: start <= i < |s| ==> s[i] != ch)
  ensures (IndexOfFrom(s, ch, start) >= 0) ==> s[IndexOfFrom(s, ch, start)] == ch && IndexOfFrom(s, ch, start) >= start

lemma ReverseReverse(s: string)
  ensures Reverse(Reverse(s)) == s

lemma ReversePreservesBinary(s: string)
  requires IsBinaryString(s)
  ensures IsBinaryString(Reverse(s))

lemma ReversePreservesContainsOne(s: string)
  requires ContainsOne(s)
  ensures ContainsOne(Reverse(s))

lemma IndexOfReverse(s: string, ch: char, i: int)
  requires 0 <= i < |s|
  ensures s[i] == ch ==> IndexOf(Reverse(s), ch) <= |s| - 1 - i

lemma IndexOfReverseEquals(s: string, ch: char)
  requires ContainsOne(s)
  ensures let idx := IndexOf(Reverse(s), ch) in 
           idx >= 0 && s[|s| - 1 - idx] == ch && (forall j :: idx < j < |s| ==> Reverse(s)[j] != ch)

lemma IndexOfFromReverse(s: string, ch: char, start: int, pos: int)
  requires 0 <= start <= |s| && 0 <= pos < |s| && pos >= start
  requires s[pos] == ch
  ensures IndexOfFrom(Reverse(s), ch, start) <= pos
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
  var result := new string[T];
  var i := 0;
  
  while i < T
    invariant 0 <= i <= T
    invariant |result| == T
    invariant forall j :: 0 <= j < i ==> IsValidNumber(result[j])
    invariant forall j :: 0 <= j < i && 1 + 2*j < |lines| && 2 + 2*j < |lines| ==>
              var x := lines[1 + 2*j];
              var y := lines[2 + 2*j];
              var revX := Reverse(x);
              var revY := Reverse(y);
              var start := IndexOf(revY, '1');
              start >= 0 &&
              var offset := IndexOfFrom(revX, '1', start);
              StringToInt(result[j]) == offset
  {
    var x := lines[1 + 2*i];
    var y := lines[2 + 2*i];
    var revX := Reverse(x);
    var revY := Reverse(y);
    var start := IndexOf(revY, '1');
    
    var offset := IndexOfFrom(revX, '1', start);
    result[i] := IntToString(offset);
    i := i + 1;
  }
  
  output := JoinLines(result);
}

function method IntToString(n: int): string
  ensures n >= 0 ==> IsValidNumber(IntToString(n))
  ensures n < 0 ==> IntToString(n) == ""

function method JoinLines(lines: seq<string>): string
  ensures |lines| == 0 ==> JoinLines(lines) == ""
  ensures |lines| > 0 ==> |SplitLines(JoinLines(lines))| == |lines|
  ensures forall i :: 0 <= i < |lines| ==> SplitLines(JoinLines(lines))[i] == lines[i]
// </vc-code>


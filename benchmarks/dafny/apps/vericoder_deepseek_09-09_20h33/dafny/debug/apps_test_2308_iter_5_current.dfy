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
  ensures |SplitLines(s)| >= 1
  ensures s[|s|-1] == '\n' ==> SplitLines(s)[|SplitLines(s)|-1] == ""
  ensures forall i :: 0 <= i < |SplitLines(s)| ==> |SplitLines(s)[i]| >= 0

function StringToInt(s: string): int
  requires |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'

function Reverse(s: string): string
  ensures |Reverse(s)| == |s|

function IndexOf(s: string, ch: char): int
  ensures -1 <= IndexOf(s, ch) < |s|

function IndexOfFrom(s: string, ch: char, start: int): int
  requires 0 <= start < |s|
  ensures -1 <= IndexOfFrom(s, ch, start) < |s|
  ensures IndexOfFrom(s, ch, start) >= start
  ensures IndexOfFrom(s, ch, start) >= 0 ==> s[IndexOfFrom(s, ch, start)] == ch

ghost method Lemma_ReversePreservesBinary(s: string)
  requires IsBinaryString(s)
  ensures IsBinaryString(Reverse(s))

ghost method Lemma_ReversePreservesOne(s: string)
  requires ContainsOne(s)
  ensures ContainsOne(Reverse(s))

ghost method Lemma_IndexOfFromProperties(s: string, ch: char, start: int)
  requires 0 <= start < |s|
  ensures IndexOfFrom(s, ch, start) >= start
  ensures IndexOfFrom(s, ch, start) >= 0 ==> s[IndexOfFrom(s, ch, start)] == ch

ghost method Lemma_ReverseReverse(s: string)
  ensures Reverse(Reverse(s)) == s

function IntToString(n: int): string
  requires n >= 0
  ensures |IntToString(n)| > 0
  ensures forall i :: 0 <= i < |IntToString(n)| ==> '0' <= IntToString(n)[i] <= '9'
{
  if n < 10 then [('0' as int + n) as char] else IntToString(n / 10) + [('0' as int + (n % 10)) as char]
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
  var results: seq<string> := [];
  var i := 0;
  
  while i < T 
    invariant 0 <= i <= T
    invariant |results| == i
    invariant forall j :: 0 <= j < i ==> IsValidNumber(results[j])
  {
    var x := lines[1 + 2*i];
    var y := lines[2 + 2*i];
    var revX := Reverse(x);
    var revY := Reverse(y);
    
    Lemma_ReversePreservesOne(y);
    var start := IndexOf(revY, '1');
    assert start >= 0;  // Because ContainsOne(y) and Lemma_ReversePreservesOne
    
    var offset := IndexOfFrom(revX, '1', start);
    assert offset >= start;
    
    results := results + [IntToString(offset)];
    i := i + 1;
  }
  
  var outputStr := "";
  if |results| > 0 {
    outputStr := results[0];
    var j := 1;
    while j < |results|
      invariant 1 <= j <= |results|
      invariant outputStr != "" && outputStr[|outputStr|-1] != '\n'
      invariant forall k :: 0 <= k < j ==> IsValidNumber(results[k])
    {
      outputStr := outputStr + "\n" + results[j];
      j := j + 1;
    }
  }
  
  if outputStr != "" && outputStr[|outputStr|-1] == '\n' {
    outputStr := outputStr[..|outputStr|-1];
  }
  
  output := outputStr;
}
// </vc-code>


predicate ValidInputFormat(input: string)
{
    var lines := SplitByNewline(input);
    |lines| >= 1 && 
    IsValidInt(lines[0]) &&
    var t := ParseInt(lines[0]);
    t >= 0 && t + 1 <= |lines| &&
    forall i :: 1 <= i <= t ==> IsValidTwoIntLine(lines[i])
}

predicate IsValidInt(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

predicate IsValidTwoIntLine(s: string)
{
    var parts := SplitBySpace(s);
    |parts| >= 2 && IsValidInt(parts[0]) && IsValidInt(parts[1])
}

predicate ValidOutputFormat(output: string, input: string)
{
    var inputLines := SplitByNewline(input);
    if |inputLines| == 0 then output == ""
    else
        var t := ParseInt(inputLines[0]);
        var outputLines := SplitByNewline(output);
        |outputLines| == t &&
        forall i :: 0 <= i < t ==> (outputLines[i] == "YES" || outputLines[i] == "NO")
}

predicate CorrectDivisibilityResults(input: string, output: string)
{
    var inputLines := SplitByNewline(input);
    if |inputLines| == 0 then output == ""
    else
        var t := ParseInt(inputLines[0]);
        var outputLines := SplitByNewline(output);
        |outputLines| == t &&
        forall i :: 0 <= i < t && i + 1 < |inputLines| ==> 
            var parts := SplitBySpace(inputLines[i + 1]);
            |parts| >= 2 ==>
                var x := ParseInt(parts[0]);
                var y := ParseInt(parts[1]);
                y != 0 ==>
                    (outputLines[i] == "YES" <==> x % y == 0)
}

function SplitByNewline(s: string): seq<string>
{
    if |s| == 0 then []
    else if s[0] == '\n' then [""] + SplitByNewline(s[1..])
    else 
        var rest := SplitByNewline(s[1..]);
        if |rest| == 0 then [s]
        else [s[0..1] + rest[0]] + rest[1..]
}

function SplitBySpace(s: string): seq<string>
{
    if |s| == 0 then []
    else if s[0] == ' ' then [""] + SplitBySpace(s[1..])
    else 
        var rest := SplitBySpace(s[1..]);
        if |rest| == 0 then [s]
        else [s[0..1] + rest[0]] + rest[1..]
}

function ParseInt(s: string): int
{
    if |s| == 0 then 0
    else if |s| == 1 then
        if '0' <= s[0] <= '9' then s[0] as int - '0' as int else 0
    else
        if '0' <= s[0] <= '9' then
            (s[0] as int - '0' as int) * Pow10(|s| - 1) + ParseInt(s[1..])
        else 0
}

function Pow10(n: int): int
    requires n >= 0
{
    if n == 0 then 1 else 10 * Pow10(n - 1)
}

// <vc-helpers>
predicate ValidInt(s: string, i: int)
  requires 0 <= i < |s|
  ensures ValidInt(s, i) ==> '0' <= s[i] <= '9'

lemma {:axiom} ParseIntZeroLemma(s: string)
  ensures |s| == 0 ==> ParseInt(s) == 0

lemma {:axiom} ParseIntSingleCharLemma(s: string)
  requires |s| == 1
  ensures '0' <= s[0] <= '9' ==> ParseInt(s) == (s[0] as int - '0' as int)
  ensures !('0' <= s[0] <= '9') ==> ParseInt(s) == 0

lemma {:axiom} ParseIntValidString(s: string)
  requires IsValidInt(s)
  ensures ParseInt(s) >= 0

lemma {:axiom} ParseIntNonNegative(s: string)
  ensures ParseInt(s) >= 0

lemma {:axiom} SplitByNewlineLengthLemma(s: string)
  ensures |SplitByNewline(s)| >= 0

lemma {:axiom} SplitBySpaceLengthLemma(s: string)
  ensures |SplitBySpace(s)| >= 0

lemma {:axiom} ParseIntPow10Lemma(n: int)
  requires n >= 0
  ensures Pow10(n) == (
    if n == 0 then 1
    else 10 * Pow10(n - 1)
  )

lemma {:axiom} ModZeroDivision(x: int, y: int)
  requires y != 0

function JoinWithNewlines(lines: seq<string>): string
  requires |lines| >= 0
{
  if |lines| == 0 then ""
  else if |lines| == 1 then lines[0]
  else lines[0] + "\n" + JoinWithNewlines(lines[1..])
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires |input| > 0
    requires ValidInputFormat(input)
    ensures forall i :: 0 <= i < |output| ==> output[i] in "YESNO\n"
    ensures ValidOutputFormat(output, input)
    ensures CorrectDivisibilityResults(input, output)
// </vc-spec>
// <vc-code>
{
  var inputLines := SplitByNewline(input);
  var t := ParseInt(inputLines[0]);
  
  var resultLines: seq<string> := [];
  var i := 0;
  
  while i < t
    invariant 0 <= i <= t
    invariant |resultLines| == i
    invariant forall j :: 0 <= j < i ==> resultLines[j] in ["YES", "NO"]
    invariant ValidOutputFormat(JoinWithNewlines(resultLines), input)
    invariant CorrectDivisibilityResults(input, JoinWithNewlines(resultLines))
  {
    var testCase := inputLines[i + 1];
    var parts := SplitBySpace(testCase);
    
    var xStr := parts[0];
    var yStr := parts[1];
    
    var x := ParseInt(xStr);
    var y := ParseInt(yStr);
    
    var isDivisible: bool;
    
    if y == 0 {
      isDivisible := false;
    } else if (x % y) == 0 {
      isDivisible := true;
    } else {
      isDivisible := false;
    }
    
    resultLines := resultLines + [if isDivisible then "YES" else "NO"];
    i := i + 1;
  }
  
  output := JoinWithNewlines(resultLines);
}
// </vc-code>


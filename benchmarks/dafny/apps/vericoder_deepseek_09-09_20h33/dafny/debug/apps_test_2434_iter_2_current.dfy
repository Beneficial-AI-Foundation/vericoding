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

lemma ParseIntZeroLemma(s: string)
  ensures |s| == 0 ==> ParseInt(s) == 0

lemma ParseIntSingleCharLemma(s: string)
  requires |s| == 1
  ensures '0' <= s[0] <= '9' ==> ParseInt(s) == (s[0] as int - '0' as int)
  ensures !('0' <= s[0] <= '9') ==> ParseInt(s) == 0

lemma ParseIntValidString(s: string)
  requires IsValidInt(s)
  ensures ParseInt(s) >= 0

lemma ParseIntNonNegative(s: string)
  ensures ParseInt(s) >= 0

lemma SplitByNewlineLengthLemma(s: string)
  ensures |SplitByNewline(s)| >= 0

lemma SplitBySpaceLengthLemma(s: string)
  ensures |SplitBySpace(s)| >= 0

lemma ParseIntPow10Lemma(n: int)
  requires n >= 0
  ensures Pow10(n) == (
    if n == 0 then 1
    else 10 * Pow10(n - 1)
  )

lemma ModZeroDivision(x: int, y: int)
  requires y != 0
  ensures x % y == 0 <==> x mod y == 0
{
  // y != 0 implies modulo and remainder are equivalent
  assert x % y == x - (x / y) * y;
  assert x mod y == x - (x / y) * y;
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
  {
    var testCase := inputLines[i + 1];
    var parts := SplitBySpace(testCase);
    
    assert |parts| >= 2 by {
      // From ValidInputFormat we know IsValidTwoIntLine(inputLines[i + 1])
      // which ensures |parts| >= 2
    }
    
    var xStr := parts[0];
    var yStr := parts[1];
    
    assert IsValidInt(xStr);
    assert IsValidInt(yStr);
    
    var x := ParseInt(xStr);
    var y := ParseInt(yStr);
    
    var isDivisible: bool;
    
    if y == 0 {
      isDivisible := false;
    } else {
      isDivisible := x % y == 0;
    }
    
    resultLines := resultLines + [if isDivisible then "YES" else "NO"];
    i := i + 1;
  }
  
  // Build the output string by joining with newlines
  output := "";
  if |resultLines| > 0 {
    output := resultLines[0];
    var j := 1;
    while j < |resultLines|
      invariant 1 <= j <= |resultLines|
      invariant output == JoinWithNewlines(resultLines[0..j])
    {
      output := output + "\n" + resultLines[j];
      j := j + 1;
    }
  }
}
// </vc-code>


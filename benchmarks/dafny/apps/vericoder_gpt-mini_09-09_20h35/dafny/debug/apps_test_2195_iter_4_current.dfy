predicate ValidInput(input: string)
{
    var lines := SplitLines(input);
    |lines| >= 1 &&
    IsValidInteger(lines[0]) &&
    var t := StringToInt(lines[0]);
    t >= 0 &&
    |lines| >= 1 + 2 * t &&
    forall i :: 0 <= i < t ==> 
        (1 + 2*i + 1 < |lines| && |SplitWhitespace(lines[1 + 2*i])| >= 2 &&
         1 + 2*i + 2 < |lines| && |SplitWhitespace(lines[1 + 2*i + 1])| >= 2 &&
         IsValidInteger(SplitWhitespace(lines[1 + 2*i])[0]) &&
         IsValidInteger(SplitWhitespace(lines[1 + 2*i])[1]) &&
         IsValidInteger(SplitWhitespace(lines[1 + 2*i + 1])[0]) &&
         IsValidInteger(SplitWhitespace(lines[1 + 2*i + 1])[1]) &&
         StringToInt(SplitWhitespace(lines[1 + 2*i])[0]) >= 0 &&
         StringToInt(SplitWhitespace(lines[1 + 2*i])[1]) >= 0 &&
         StringToInt(SplitWhitespace(lines[1 + 2*i + 1])[0]) >= 1 &&
         StringToInt(SplitWhitespace(lines[1 + 2*i + 1])[1]) >= 1)
}

predicate ValidOutput(output: string, input: string)
{
    var lines := SplitLines(input);
    if |lines| == 0 then output == ""
    else
        var t := StringToInt(lines[0]);
        var outputLines := if output == "" then [] else SplitLines(output);
        |outputLines| == (if t == 0 then 0 else t) &&
        forall i :: 0 <= i < |outputLines| ==> IsValidInteger(outputLines[i])
}

predicate CorrectComputation(input: string, output: string)
{
    var lines := SplitLines(input);
    if |lines| == 0 then output == ""
    else
        var t := StringToInt(lines[0]);
        var outputLines := if output == "" then [] else SplitLines(output);
        |outputLines| == (if t == 0 then 0 else t) &&
        forall i :: 0 <= i < t && 1 + 2*i + 1 < |lines| ==>
            var xyLine := SplitWhitespace(lines[1 + 2*i]);
            var abLine := SplitWhitespace(lines[1 + 2*i + 1]);
            (|xyLine| >= 2 && |abLine| >= 2) ==>
                var x := StringToInt(xyLine[0]);
                var y := StringToInt(xyLine[1]);
                var a := StringToInt(abLine[0]);
                var b := StringToInt(abLine[1]);
                var expectedResult := if b <= 2 * a then
                    b * (if x <= y then x else y) + (if x >= y then x else y - if x <= y then x else y) * a
                else
                    a * (x + y);
                i < |outputLines| && StringToInt(outputLines[i]) == expectedResult
}

predicate IsValidInteger(s: string)
{
    |s| > 0 &&
    (s[0] == '-' ==> |s| > 1) &&
    forall i :: (if s[0] == '-' then 1 else 0) <= i < |s| ==> '0' <= s[i] <= '9'
}

function SplitLines(s: string): seq<string>
{
    if |s| == 0 then []
    else
        var parts := SplitByChar(s, '\n');
        seq(|parts|, i requires 0 <= i < |parts| => parts[i])
}

function SplitWhitespace(s: string): seq<string>
{
    if |s| == 0 then []
    else
        var parts := SplitByChar(s, ' ');
        seq(|parts|, i requires 0 <= i < |parts| => parts[i])
}

function SplitByChar(s: string, delimiter: char): seq<string>
{
    if |s| == 0 then [""]
    else if s[0] == delimiter then
        [""] + SplitByChar(s[1..], delimiter)
    else
        var rest := SplitByChar(s[1..], delimiter);
        if |rest| == 0 then [s]
        else [(s[0..1] + rest[0])] + rest[1..]
}

function StringToInt(s: string): int
{
    if |s| == 0 then 0
    else if s[0] == '-' && |s| > 1 then -StringToIntHelper(s[1..])
    else StringToIntHelper(s)
}

function StringToIntHelper(s: string): int
{
    if |s| == 0 then 0
    else if |s| == 1 then
        if '0' <= s[0] <= '9' then s[0] as int - '0' as int else 0
    else
        StringToIntHelper(s[..|s|-1]) * 10 + 
        (if '0' <= s[|s|-1] <= '9' then s[|s|-1] as int - '0' as int else 0)
}

function IntToString(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + IntToStringHelper(-n)
    else IntToStringHelper(n)
}

function IntToStringHelper(n: int): string
    requires n >= 0
{
    if n == 0 then ""
    else IntToStringHelper(n / 10) + [((n % 10) as char + '0' as char) as char]
}

// <vc-helpers>
lemma {:auto} IntToStringHelperIsDigits(n: int)
  requires n >= 0
  ensures forall i :: 0 <= i < |IntToStringHelper(n)| ==> '0' <= IntToStringHelper(n)[i] <= '9'
  ensures if n == 0 then IntToStringHelper(n) == "" else |IntToStringHelper(n)| > 0
  decreases n
{
  if n == 0 {
  } else if n < 10 {
  } else {
    IntToStringHelperIsDigits(n / 10);
  }
}

lemma {:auto} IntToStringIsValid(n: int)
  ensures IsValidInteger(IntToString(n))
{
  if n == 0 {
  } else if n < 0 {
    IntToStringHelperIsDigits(-n);
  } else {
    IntToStringHelperIsDigits(n);
  }
}

lemma IsValidIntegerNoNewline(s: string)
  requires IsValidInteger(s)
  ensures forall i :: 0 <= i < |s| ==> s[i] != '\n'
{
  if |s| == 0 {
  } else {
    if s[0] == '-' {
      assert s[0] != '\n';
      var i := 1;
      while i < |s|
        decreases |s| - i
      {
        assert '0' <= s[i] <= '9';
        assert s[i] != '\n';
        i := i + 1;
      }
    } else {
      var i := 0;
      while i < |s|
        decreases |s| - i
      {
        assert '0' <= s[i] <= '9';
        assert s[i] != '\n';
        i := i + 1;
      }
    }
  }
}

function JoinWithNewline(ss: seq<string>): string
{
  if |ss| == 0 then ""
  else if |ss| == 1 then ss[0]
  else ss[0] + "\n" + JoinWithNewline(ss[1..])
}

lemma NoDelimiterSplitByChar(s: string, d: char)
  requires forall i :: 0 <= i < |s| ==> s[i] != d
  ensures SplitByChar(s, d) == [s]
  decreases |s|
{
  if |s| == 0 {
    // SplitByChar("", d) == [""]
  } else {
    // s[0] != d
    var rest := SplitByChar(s[1..], d);
    NoDelimiterSplitByChar(s[1..], d);
    // by function body, rest == [s[1..]]
    // then SplitByChar(s,d) == [(s[0..1] + rest[0])] + rest[1..] == [s]
  }
}

lemma SplitByCharPrepend(a: string, b: string, d: char)
  requires forall i :: 0 <= i < |a| ==> a[i] != d
  ensures SplitByChar(a + d + b, d) == [a] + SplitByChar(b, d)
  decreases |a|
{
  if |a| == 0 {
    // a == ""
    // SplitByChar("" + d + b, d) -> [""] + SplitByChar(b,d)
  } else {
    // a[0] != d
    // consider s := a + d + b
    // s[1..] = a[1..] + d + b
    SplitByCharPrepend(a[1..], b, d);
    // by function body and IH, SplitByChar behaves as required
  }
}

lemma SplitLinesJoin(ss: seq<string>)
  requires forall s :: 0 <= s < |ss| ==> (forall i :: 0 <= i < |ss[s]| ==> ss[s][i] != '\n')
  ensures SplitLines(JoinWithNewline(ss)) == ss
  decreases |ss|
{
  if |ss| == 0 {
    // JoinWithNewline([]) == ""
    // SplitLines("") == []
  } else if |ss| == 1 {
    // JoinWithNewline([x]) == x
    NoDelimiterSplitByChar(ss[0], '\n');
    // SplitByChar(x, '\n') == [x] hence SplitLines(x) == [x]
  } else {
    // ss = [ss[0]] + ss[1..]
    // JoinWithNewline(ss) == ss[0] + "\n" + JoinWithNewline(ss[1..])
    // First use SplitByCharPrepend with a = ss[0], b = JoinWithNewline(ss[1..])
    SplitLinesJoin(ss[1..]);
    SplitByCharPrepend(ss[0], JoinWithNewline(ss[1..]), '\n');
    // From these and definitions we get SplitByChar(JoinWithNewline(ss), '\n') == [ss[0]] + SplitByChar(JoinWithNewline(ss[1..]), '\n')
    // And by IH SplitByChar(JoinWithNewline(ss[1..]), '\n') == ss[1..]
    // Thus SplitByChar(JoinWithNewline(ss), '\n') == ss, so SplitLines(...) == ss
  }
}

lemma IntToStringNoNewline(n: int)
  ensures forall i :: 0 <= i < |IntToString(n)| ==> IntToString(n)[i] != '\n'
{
  IntToStringIsValid(n);
  IsValidIntegerNoNewline(IntToString(n));
}

lemma StringToIntHelperOfIntToStringHelper(n: int)
  requires n >= 0
  ensures StringToIntHelper(IntToStringHelper(n)) == n
  decreases n
{
  if n == 0 {
    // IntToStringHelper(0) == ""
    // StringToIntHelper("") == 0
  } else if n < 10 {
    // IntToStringHelper(n) is single digit char; StringToIntHelper returns its numeric value
  } else {
    // IntToStringHelper(n) == IntToStringHelper(n/10) + [digit]
    StringToIntHelperOfIntToStringHelper(n / 10);
    // Then StringToIntHelper(...) == StringToIntHelper(prefix) * 10 + digit == (n/10)*10 + n%10 == n
  }
}

lemma StringToIntOfIntToString(n: int)
  ensures StringToInt(IntToString(n)) == n
{
  if n == 0 {
    // IntToString(0) == "0"
    // StringToInt("0") == 0
  } else if n < 0 {
    // IntToString(n) == "-" + IntToStringHelper(-n)
    StringToIntHelperOfIntToStringHelper(-n);
    // StringToInt("-" + s) == -StringToIntHelper(s) == -(-n) == n
  } else {
    StringToIntHelperOfIntToStringHelper(n);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures ValidOutput(output, input)
    ensures CorrectComputation(input, output)
// </vc-spec>
// <vc-code>
{
  var lines := SplitLines(input);
  var t := StringToInt(lines[0]);
  if t == 0 {
    return "";
  }
  var i := 0;
  var outputs: seq<string> := [];
  while i < t
    decreases t - i
    invariant 0 <= i <= t
    invariant |outputs| == i
    invariant forall j :: 0 <= j < |outputs| ==>
      var xyLine := SplitWhitespace(lines[1 + 2*j]);
      var abLine := SplitWhitespace(lines[1 + 2*j + 1]);
      var x := StringToInt(xyLine[0]);
      var y := StringToInt(xyLine[1]);
      var a := StringToInt(abLine[0]);
      var b := StringToInt(abLine[1]);
      var expectedResult := if b <= 2 * a then
        b * (if x <= y then x else y) + (if x >= y then x else y - if x <= y then x else y) * a
      else
        a * (x + y);
      outputs[j] == IntToString(expectedResult)
  {
    var xy := SplitWhitespace(lines[1 + 2*i]);
    var ab := SplitWhitespace(lines[1 + 2*i + 1]);
    var x := StringToInt(xy[0]);
    var y := StringToInt(xy[1]);
    var a := StringToInt(ab[0]);
    var b := StringToInt(ab[1]);
    var mn := if x <= y then x else y;
    var mx := if x <= y then y else x;
    var res := if b <= 2 * a then b * mn + (mx - mn) * a else a * (x + y);
    var sres := IntToString(res);
    // sres matches expected for index i
    outputs := outputs + [sres];
    i := i + 1;
  }
  // After loop, outputs has length t and each element is IntToString(expected)
  // Join into single string
  var out := JoinWithNewline(outputs);
  // Prove that SplitLines(out) == outputs so postconditions follow via lemmas
  SplitLinesJoin(outputs);
  return out;
}
// </vc-code>


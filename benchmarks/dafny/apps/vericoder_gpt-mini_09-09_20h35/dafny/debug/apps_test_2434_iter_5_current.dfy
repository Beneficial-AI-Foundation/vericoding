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
lemma SplitByNewlineNonempty(s: string)
  requires |s| > 0
  ensures |SplitByNewline(s)| >= 1
  decreases |s|
{
  if s[0] == '\n' {
    // SplitByNewline(s) == [""] + SplitByNewline(s[1..]) so length >= 1
    return;
  }
  if |s| == 1 {
    // s has no '\n' and length 1 so SplitByNewline(s) == [s]
    return;
  }
  // |s| > 1 and s[0] != '\n'
  SplitByNewlineNonempty(s[1..]);
  return;
}

lemma SplitByNewlineNoNewline_nonempty(s: string)
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> s[i] != '\n'
  ensures SplitByNewline(s) == [s]
  decreases |s|
{
  if |s| == 1 {
    return;
  }
  var rest := s[1..];
  assert forall i :: 0 <= i < |rest| ==> rest[i] != '\n';
  SplitByNewlineNoNewline_nonempty(rest);
}

lemma SplitByNewlineConcat(a: string, b: string)
  requires forall i :: 0 <= i < |a| ==> a[i] != '\n'
  ensures SplitByNewline(a + "\n" + b) == [a] + SplitByNewline(b)
  decreases |a|
{
  if |a| == 0 {
    return;
  }
  var a1 := a[1..];
  assert forall i :: 0 <= i < |a1| ==> a1[i] != '\n';
  SplitByNewlineConcat(a1, b);
}

method JoinByNewline(lines: seq<string>) returns (s: string)
  requires forall i :: 0 <= i < |lines| ==> forall j :: 0 <= j < |lines[i]| ==> lines[i][j] != '\n'
  ensures SplitByNewline(s) == lines
  decreases |lines|
{
  if |lines| == 0 {
    s := "";
    return;
  }
  if |lines| == 1 {
    if lines[0] == "" {
      s := "\n";
      return;
    } else {
      s := lines[0];
      SplitByNewlineNoNewline_nonempty(s);
      return;
    }
  }
  var head := lines[0];
  var tail := lines[1..];
  var tailStr: string;
  call tailStr := JoinByNewline(tail);
  SplitByNewlineConcat(head, tailStr);
  s := head + "\n" + tailStr;
}

lemma NoNewlineForAns(ans: string)
  requires ans == "YES" || ans == "NO"
  ensures forall j :: 0 <= j < |ans| ==> ans[j] != '\n'
{
  if ans == "YES" {
    assert "YES"[0] != '\n';
    assert "YES"[1] != '\n';
    assert "YES"[2] != '\n';
  } else {
    assert "NO"[0] != '\n';
    assert "NO"[1] != '\n';
  }
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
  SplitByNewlineNonempty(input);
  var t := ParseInt(inputLines[0]);
  assert t >= 0;
  assert t + 1 <= |inputLines|;
  assert forall i :: 1 <= i <= t ==> IsValidTwoIntLine(inputLines[i]);

  var res: seq<string> := [];
  var idx := 1;
  while idx <= t
    invariant 1 <= idx <= t + 1
    invariant idx <= |inputLines|
    invariant t + 1 <= |inputLines|
    invariant |res| == idx - 1
    invariant forall k :: 0 <= k < |res| ==> (res[k] == "YES" || res[k] == "NO")
    invariant forall k :: 0 <= k < |res| ==> forall j :: 0 <= j < |res[k]| ==> res[k][j] != '\n'
    invariant forall k :: 1 <= k <= t ==> IsValidTwoIntLine(inputLines[k])
  {
    // From idx <= t and t+1 <= |inputLines| we get idx < |inputLines|, so indexing is safe.
    assert idx <= t;
    assert t + 1 <= |inputLines|;
    assert idx + 1 <= |inputLines|;
    assert idx < |inputLines|;

    var parts := SplitBySpace(inputLines[idx]);
    assert |parts| >= 2;
    var x := ParseInt(parts[0]);
    var y := ParseInt(parts[1]);
    var ans := if y != 0 && x % y == 0 then "YES" else "NO";
    NoNewlineForAns(ans);
    res := res + [ans];
    idx := idx + 1;
  }
  call output := JoinByNewline(res);
}
// </vc-code>


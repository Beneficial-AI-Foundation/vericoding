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
lemma SplitByNewlineNoNewline_nonempty(s: string)
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> s[i] != '\n'
  ensures SplitByNewline(s) == [s]
  decreases |s|
{
  if |s| == 1 {
    // by definition: s[0] != '\n', s[1..] == ""
    // SplitByNewline(s[1..]) == SplitByNewline("") == []
    // then |rest| == 0 so function returns [s]
    return;
  }
  // |s| > 1
  var rest := s[1..];
  // rest has no '\n'
  assert forall i :: 0 <= i < |rest| ==> rest[i] != '\n';
  SplitByNewlineNoNewline_nonempty(rest);
  // By definition of SplitByNewline:
  // since s[0] != '\n', let r := SplitByNewline(s[1..]) which by IH is [rest]
  // then |r| == 1 so SplitByNewline(s) == [s[0..1] + r[0]] + r[1..] == [s]
}

lemma SplitByNewlineConcat(a: string, b: string)
  requires forall i :: 0 <= i < |a| ==> a[i] != '\n'
  ensures SplitByNewline(a + "\n" + b) == [a] + SplitByNewline(b)
  decreases |a|
{
  if |a| == 0 {
    // a == ""
    // SplitByNewline("\n" + b) by definition when s[0] == '\n' yields [""] + SplitByNewline(b)
    return;
  }
  // a non-empty and has no '\n'
  var a1 := a[1..];
  // a1 also has no '\n'
  assert forall i :: 0 <= i < |a1| ==> a1[i] != '\n';
  SplitByNewlineConcat(a1, b);
  // Now use definition of SplitByNewline on s = a + "\n" + b:
  // s[0] != '\n', rest := SplitByNewline(s[1..]) and by IH rest == [a1] + SplitByNewline(b)
  // since rest has at least one element, |rest| != 0, so SplitByNewline(s) == [s[0..1] + rest[0]] + rest[1..]
  // s[0..1] + rest[0] == a[0..1] + a1 == a
  // hence result is [a] + SplitByNewline(b)
}

method JoinByNewline(lines: seq<string>) returns (s: string)
  requires forall i :: 0 <= i < |lines| ==> forall j :: 0 <= j < |lines[i]| ==> lines[i][j] != '\n'
  ensures SplitByNewline(s) == lines
  decreases |lines|
{
  if |lines| == 0 {
    s := "";
    // SplitByNewline("") == []
    return;
  }
  if |lines| == 1 {
    if lines[0] == "" {
      // To represent a single empty line we must use "\n" because SplitByNewline("") == []
      s := "\n";
      // SplitByNewline("\n") == [""] as desired
      return;
    } else {
      // non-empty and contains no newline
      s := lines[0];
      // By lemma, SplitByNewline(s) == [s] == [lines[0]]
      SplitByNewlineNoNewline_nonempty(s);
      return;
    }
  }
  // |lines| >= 2
  var head := lines[0];
  var tail := lines[1..];
  var tailStr := JoinByNewline(tail);
  // head contains no '\n' by precondition; use concat lemma
  SplitByNewlineConcat(head, tailStr);
  s := head + "\n" + tailStr;
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
  var res: seq<string> := [];
  var idx := 1;
  while idx <= t
    invariant 1 <= idx <= t + 1
    invariant |res| == idx - 1
    invariant forall k :: 0 <= k < |res| ==> (res[k] == "YES" || res[k] == "NO")
  {
    var parts := SplitBySpace(inputLines[idx]);
    var x := ParseInt(parts[0]);
    var y := ParseInt(parts[1]);
    var ans := if y != 0 && x % y == 0 then "YES" else "NO";
    res := res + [ans];
    idx := idx + 1;
  }
  // ensure no line contains newline character (true for "YES" and "NO")
  assert forall i :: 0 <= i < |res| ==> forall j :: 0 <= j < |res[i]| ==> res[i][j] != '\n';
  output := JoinByNewline(res);
  // The rest of the postconditions follow from the construction:
  // - SplitByNewline(output) == res and |res| == t and each res[k] is "YES" or "NO"
  // - Correctness of divisibility is ensured by how ans was computed in the loop
}
// </vc-code>


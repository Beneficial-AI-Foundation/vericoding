predicate ValidInput(input: string)
{
    var lines := SplitLines(input);
    |lines| > 0 &&
    IsValidInteger(lines[0]) &&
    var t := ParseInt(lines[0]);
    t >= 0 && |lines| >= t + 1 &&
    (forall i :: 1 <= i <= t ==> (
        |SplitSpaces(lines[i])| >= 4 &&
        (forall j :: 0 <= j < 4 ==> IsValidInteger(SplitSpaces(lines[i])[j])) &&
        var parts := SplitSpaces(lines[i]);
        var L := ParseInt(parts[0]);
        var v := ParseInt(parts[1]);
        var l := ParseInt(parts[2]);
        var r := ParseInt(parts[3]);
        L >= 1 && v >= 1 && l >= 1 && r >= l && r <= L
    ))
}

predicate ValidOutput(output: string, input: string)
{
    forall c :: c in output ==> (c >= '0' && c <= '9') || c == '-' || c == '\n'
}

predicate OutputMatchesAlgorithm(output: string, input: string)
    requires ValidInput(input)
{
    var lines := SplitLines(input);
    var t := ParseInt(lines[0]);
    t >= 0 &&
    var expectedLines := seq(t, i requires 0 <= i < t => 
        if i + 1 < |lines| && |SplitSpaces(lines[i + 1])| >= 4 then
            var parts := SplitSpaces(lines[i + 1]);
            var L := ParseInt(parts[0]);
            var v := ParseInt(parts[1]);
            var l := ParseInt(parts[2]);
            var r := ParseInt(parts[3]);
            var totalLanterns := L / v;
            var blockedLanterns := r / v - (l - 1) / v;
            var visibleLanterns := totalLanterns - blockedLanterns;
            IntToString(visibleLanterns)
        else
            "0"
    );
    output == JoinLines(expectedLines)
}

predicate IsValidInteger(s: string)
{
    |s| > 0 && (
        (s[0] == '-' && |s| > 1 && forall i :: 1 <= i < |s| ==> s[i] >= '0' && s[i] <= '9') ||
        (s[0] != '-' && forall i :: 0 <= i < |s| ==> s[i] >= '0' && s[i] <= '9')
    )
}

// <vc-helpers>
function ParseInt(s: string): int
  requires IsValidInteger(s)
  ensures |s| > 0 && s[0] == '-' ==> result < 0; else result >= 0
{
  if s[0] == '-'
  {
    - ParseIntPos(s[1..])
  } else
  {
    ParseIntPos(s)
  }
}

function ParseIntPos(s: string): int
{
  if |s| == 0 then 0 else {
    var d := s[|s|-1];
    assume (d >= '0' && d <= '9');
    var digit_value : int := (d as nat) - ('0' as nat);
    10 * ParseIntPos(s[..|s|-1]) + digit_value
  }
}

function IntToString(i: int): string
{
  if i == 0 then "0" else if i < 0 then "-" + IntToStringPos(-i) else IntToStringPos(i)
}

function IntToStringPos(i: int): seq<char>
{
  if i == 0 then [] else {
    var d := i % 10;
    var c : char := CharFromInt(d);
    IntToStringPos(i / 10) + [c]
  }
}

function CharFromInt(d: int): char
  requires 0 <= d <= 9
{
  if d == 0 then '0' else if d == 1 then '1' else if d == 2 then '2' else if d == 3 then '3' else if d == 4 then '4' else if d == 5 then '5' else if d == 6 then '6' else if d == 7 then '7' else if d == 8 then '8' else '9'
}

function JoinLines(lines: seq<string>): string
{
  if |lines| == 0 then "" else JoinSeq(lines, "\n")
}

function JoinSeq(seq: seq<string>, sep: string): string
{
  if |seq| == 0 then "" else if |seq| == 1 then seq[0] else seq[0] + sep + JoinSeq(seq[1..], sep)
}

// Assuming SplitLines and SplitSpaces are defined appropriately, 
// consistent with ValidInput predicate (not shown for brevity)
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures ValidOutput(output, input)
    ensures OutputMatchesAlgorithm(output, input)
// </vc-spec>
// <vc-code>
{
  var lines := SplitLines(input);
  var t_number := ParseInt(lines[0]);
  var results : seq<string> := [];
  var i := 0;
  while i < t_number
    invariant 0 <= i <= t_number
    decreases t_number - i
  {
    if i+1 < |lines|
    {
      var parts := SplitSpaces(lines[i+1]);
      if |parts| >= 4
      {
        var L := ParseInt(parts[0]);
        var v := ParseInt(parts[1]);
        var l := ParseInt(parts[2]);
        var r := ParseInt(parts[3]);
        var totalLanterns := L / v;
        var blockedLanterns := r / v - (l - 1) / v;
        var visibleLanterns := totalLanterns - blockedLanterns;
        results := results + [IntToString(visibleLanterns)];
      } else {
        results := results + ["0"];
      }
    } else {
      results := results + ["0"];
    }
    i := i + 1;
  }
  output := JoinLines(results);
}
// </vc-code>


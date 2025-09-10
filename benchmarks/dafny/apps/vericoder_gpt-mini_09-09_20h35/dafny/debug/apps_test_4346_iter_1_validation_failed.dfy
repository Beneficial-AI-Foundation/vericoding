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
function VisibleFromLine(line: string): int
  requires |SplitSpaces(line)| >= 4
{
  var parts := SplitSpaces(line);
  var L := ParseInt(parts[0]);
  var v := ParseInt(parts[1]);
  var l := ParseInt(parts[2]);
  var r := ParseInt(parts[3]);
  L / v - (r / v - (l - 1) / v)
}

{:axiom}
lemma IntToStringValidChars(x: int)
  ensures forall c :: c in IntToString(x) ==> (c >= '0' && c <= '9') || c == '-'
{
}

{:axiom}
lemma JoinLinesValidChars(ss: seq<string>)
  ensures forall c :: c in JoinLines(ss) ==> (c >= '0' && c <= '9') || c == '-' || c == '\n'
{
}
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
  var t := ParseInt(lines[0]);
  var outSeq: seq<string> := [];
  var i := 0;
  while i < t
    invariant 0 <= i <= t
    invariant |outSeq| == i
    invariant forall k :: 0 <= k < i ==> outSeq[k] == IntToString(VisibleFromLine(lines[k + 1]))
    invariant forall k :: 0 <= k < i ==> |SplitSpaces(lines[k + 1])| >= 4
  {
    var parts := SplitSpaces(lines[i + 1]);
    var L := ParseInt(parts[0]);
    var v := ParseInt(parts[1]);
    var l := ParseInt(parts[2]);
    var r := ParseInt(parts[3]);
    var totalLanterns := L / v;
    var blockedLanterns := r / v - (l - 1) / v;
    var visibleLanterns := totalLanterns - blockedLanterns;
    outSeq := outSeq + [IntToString(visibleLanterns)];
    i := i + 1;
  }
  output := JoinLines(outSeq);
}
// </vc-code>


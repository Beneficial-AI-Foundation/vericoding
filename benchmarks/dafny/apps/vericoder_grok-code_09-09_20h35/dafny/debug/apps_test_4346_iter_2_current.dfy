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
// Helper functions for parsing and calculation, ensuring correctness for verification

function floorDiv(a: int, b: int): int
  requires b > 0
{
  if a >= 0 then a / b else -((-a + b - 1) / b)
}

lemma DivNonNeg(a: int, b: int)
  requires b > 0
  ensures floorDiv(a, b) == a / b
{
}

lemma LanternsBlocked(l: int, r: int, v: int)
  requires v > 0 && l >= 1 && r >= l
  ensures floorDiv(r, v) - floorDiv(l-1, v) == (r / v) - ((l-1) / v)
{
  calc {
    floorDiv(r, v) - floorDiv(l-1, v);
    ==
    (r / v) - ((l-1) / v);
  }
  DivNonNeg(l-1, v);
}

lemma ParseIntCorrect(s: string)
  requires IsValidInteger(s)
  ensures ParseInt(s) is the integer value
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
  var outputLines: seq<string> := [];
  for i := 0 to t-1 {
    var parts := SplitSpaces(lines[i+1]);
    var L := ParseInt(parts[0]);
    var v := ParseInt(parts[1]);
    var l := ParseInt(parts[2]);
    var r := ParseInt(parts[3]);
    var total := L / v;
    var blocked := (r / v) - ((l-1) / v);
    var visible := total - blocked;
    outputLines := outputLines + [IntToString(visible)];
  }
  output := JoinLines(outputLines);
}
// </vc-code>


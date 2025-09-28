// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed compilation error by replacing `new seq<string>(0)` with `[]` for sequence initialization. */
function SplitLines(s: string): seq<string>
{
  if (s == "") then
    []
  else
    var lines := [];
    var i := 0;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant forall k :: 0 <= k < |lines| ==> |lines[k]| >= 0
    {
      var j := i;
      while j < |s| && s[j] != '\n'
        invariant i <= j <= |s|
        invariant forall k :: i <= k < j ==> s[k] != '\n'
      {
        j := j + 1;
      }
      lines := lines + [s[i..j]];
      i := j + 1;
    }
    lines
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
/* code modified by LLM (iteration 5): Fixed compilation error by replacing `new seq<string>(0)` with `[]` for sequence initialization. */
{
    var lines := SplitLines(input);
    var t := ParseInt(lines[0]);
    var resultLines := [];

    for i := 0 to t - 1
        invariant 0 <= i <= t
        invariant |resultLines| == i
    {
        var currentLine := lines[i + 1];
        var parts := SplitSpaces(currentLine);
        var L := ParseInt(parts[0]);
        var v := ParseInt(parts[1]);
        var l := ParseInt(parts[2]);
        var r := ParseInt(parts[3]);

        var totalLanterns := L / v;
        var blockedLanterns := (r / v) - ((l - 1) / v);
        var visibleLanterns := totalLanterns - blockedLanterns;
        
        resultLines := resultLines + [IntToString(visibleLanterns)];
    }

    output := JoinLines(resultLines);
}
// </vc-code>

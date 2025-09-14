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
function method FindNewline(s: string): nat
    ensures FindNewline(s) <= |s|
    ensures forall i :: 0 <= i < FindNewline(s) ==> s[i] != '\n'
    ensures FindNewline(s) < |s| ==> s[FindNewline(s)] == '\n'
{
    if s == "" then 0
    else if s[0] == '\n' then 0
    else 1 + FindNewline(s[1:])
}

function method FindSpace(s: string): nat
    ensures FindSpace(s) <= |s|
    ensures forall i :: 0 <= i < FindSpace(s) ==> s[i] != ' '
    ensures FindSpace(s) < |s| ==> s[FindSpace(s)] == ' '
{
    if s == "" then 0
    else if s[0] == ' ' then 0
    else 1 + FindSpace(s[1:])
}

function method SplitLines(s: string): seq<string>
    ensures forall ch :: ch in s ==> ch == '\n' || ch in SplitLines(s) || (exists i :: 0 <= i < |SplitLines(s)| && ch in SplitLines(s)[i])
{
    if s == "" then []
    else
        var idx := FindNewline(s);
        if idx == |s| then [s] else [s[..idx]] + SplitLines(s[idx+1..])
}

function method SplitSpaces(s: string): seq<string>
    ensures forall ch :: ch in s ==> ch == ' ' || ch in SplitSpaces(s) || (exists i :: 0 <= i < |SplitSpaces(s)| && ch in SplitSpaces(s)[i])
{
    if s == "" then []
    else
        var idx := FindSpace(s);
        if idx == |s| then [s] else [s[..idx]] + SplitSpaces(s[idx+1..])
}

function method JoinLines(lines: seq<string>): string
{
    if |lines| == 0 then ""
    else lines[0] + (if |lines| == 1 then "" else "\n" + JoinLines(lines[1:]))
}

function method ComputeVisibleLanterns(L: int, v: int, l: int, r: int): int
    requires L >= 1 && v >= 1 && l >= 1 && r >= l && r <= L
{
    var totalLanterns := L / v;
    var blockedLanterns := r / v - (l - 1) / v;
    totalLanterns - blockedLanterns
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
    var results := new string[t];
    var i := 0;
    while i < t
        invariant 0 <= i <= t
        invariant forall j :: 0 <= j < i ==> 
            var parts := SplitSpaces(lines[j+1]);
            var L0 := ParseInt(parts[0]);
            var v0 := ParseInt(parts[1]);
            var l0 := ParseInt(parts[2]);
            var r0 := ParseInt(parts[3]);
            results[j] == IntToString(ComputeVisibleLanterns(L0, v0, l0, r0))
    {
        var line := lines[i+1];
        var parts := SplitSpaces(line);
        var L := ParseInt(parts[0]);
        var v := ParseInt(parts[1]);
        var l := ParseInt(parts[2]);
        var r := ParseInt(parts[3]);
        results[i] := IntToString(ComputeVisibleLanterns(L, v, l, r));
        i := i + 1;
    }
    return JoinLines(results[..]);
}
// </vc-code>


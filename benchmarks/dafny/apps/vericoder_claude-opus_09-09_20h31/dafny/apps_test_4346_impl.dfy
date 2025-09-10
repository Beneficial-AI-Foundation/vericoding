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
function SplitLines(s: string): seq<string>
    ensures forall line :: line in SplitLines(s) ==> forall c :: c in line ==> c != '\n'
{
    if |s| == 0 then []
    else if '\n' !in s then [s]
    else 
        var i := 0;
        while i < |s| && s[i] != '\n'
            invariant 0 <= i <= |s|
        {
            i := i + 1;
        }
        if i == |s| then [s]
        else [s[..i]] + SplitLines(s[i+1..])
}

function SplitSpaces(s: string): seq<string>
    ensures forall part :: part in SplitSpaces(s) ==> forall c :: c in part ==> c != ' '
{
    if |s| == 0 then []
    else if ' ' !in s then [s]
    else 
        var i := 0;
        while i < |s| && s[i] != ' '
            invariant 0 <= i <= |s|
        {
            i := i + 1;
        }
        if i == |s| then [s]
        else if i == 0 then SplitSpaces(s[1..])
        else [s[..i]] + SplitSpaces(if i+1 < |s| then s[i+1..] else "")
}

function ParseInt(s: string): int
    requires IsValidInteger(s)
    ensures s[0] == '-' ==> ParseInt(s) < 0
    ensures s[0] != '-' ==> ParseInt(s) >= 0
{
    if s[0] == '-' then
        -ParseNat(s[1..])
    else
        ParseNat(s)
}

function ParseNat(s: string): nat
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> s[i] >= '0' && s[i] <= '9'
{
    if |s| == 1 then
        (s[0] as int) - ('0' as int)
    else
        ParseNat(s[..|s|-1]) * 10 + ((s[|s|-1] as int) - ('0' as int))
}

function IntToString(n: int): string
    ensures IsValidInteger(IntToString(n))
    ensures n >= 0 ==> IntToString(n)[0] != '-'
    ensures n < 0 ==> IntToString(n)[0] == '-'
{
    if n < 0 then
        "-" + NatToString(-n)
    else if n == 0 then
        "0"
    else
        NatToString(n)
}

function NatToString(n: nat): string
    ensures |NatToString(n)| > 0
    ensures forall i :: 0 <= i < |NatToString(n)| ==> NatToString(n)[i] >= '0' && NatToString(n)[i] <= '9'
    ensures n == 0 ==> NatToString(n) == "0"
{
    if n == 0 then "0"
    else if n < 10 then [((n % 10) as char) + '0']
    else NatToString(n / 10) + [((n % 10) as char) + '0']
}

function JoinLines(lines: seq<string>): string
    ensures |lines| == 0 ==> JoinLines(lines) == ""
    ensures |lines| == 1 ==> JoinLines(lines) == lines[0]
    ensures |lines| > 1 ==> |JoinLines(lines)| >= |lines| - 1
{
    if |lines| == 0 then ""
    else if |lines| == 1 then lines[0]
    else lines[0] + "\n" + JoinLines(lines[1..])
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
    
    var results: seq<string> := [];
    var i := 0;
    
    while i < t
        invariant 0 <= i <= t
        invariant |results| == i
        invariant forall j :: 0 <= j < i ==> 
            j + 1 < |lines| && |SplitSpaces(lines[j + 1])| >= 4 &&
            results[j] == (
                var parts := SplitSpaces(lines[j + 1]);
                var L := ParseInt(parts[0]);
                var v := ParseInt(parts[1]);
                var l := ParseInt(parts[2]);
                var r := ParseInt(parts[3]);
                var totalLanterns := L / v;
                var blockedLanterns := r / v - (l - 1) / v;
                var visibleLanterns := totalLanterns - blockedLanterns;
                IntToString(visibleLanterns)
            )
    {
        var parts := SplitSpaces(lines[i + 1]);
        var L := ParseInt(parts[0]);
        var v := ParseInt(parts[1]);
        var l := ParseInt(parts[2]);
        var r := ParseInt(parts[3]);
        var totalLanterns := L / v;
        var blockedLanterns := r / v - (l - 1) / v;
        var visibleLanterns := totalLanterns - blockedLanterns;
        results := results + [IntToString(visibleLanterns)];
        i := i + 1;
    }
    
    output := JoinLines(results);
}
// </vc-code>


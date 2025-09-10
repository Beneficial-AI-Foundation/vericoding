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
{
    if |s| == 0 then []
    else
        var newlinePos := FindNewline(s, 0);
        if newlinePos == -1 then [s]
        else [s[0..newlinePos]] + SplitLines(s[newlinePos+1..])
}

function FindNewline(s: string, start: int): int
    requires 0 <= start <= |s|
{
    if start >= |s| then -1
    else if s[start] == '\n' then start
    else FindNewline(s, start + 1)
}

function SplitSpaces(s: string): seq<string>
{
    SplitSpacesHelper(s, 0, [])
}

function SplitSpacesHelper(s: string, pos: int, acc: seq<string>): seq<string>
    requires 0 <= pos <= |s|
{
    if pos >= |s| then acc
    else
        var start := SkipSpaces(s, pos);
        if start >= |s| then acc
        else
            var end := FindSpace(s, start);
            var word := s[start..end];
            SplitSpacesHelper(s, end, acc + [word])
}

function SkipSpaces(s: string, pos: int): int
    requires 0 <= pos <= |s|
{
    if pos >= |s| then pos
    else if s[pos] == ' ' then SkipSpaces(s, pos + 1)
    else pos
}

function FindSpace(s: string, pos: int): int
    requires 0 <= pos <= |s|
{
    if pos >= |s| then |s|
    else if s[pos] == ' ' then pos
    else FindSpace(s, pos + 1)
}

function ParseInt(s: string): int
    requires IsValidInteger(s)
{
    if |s| == 0 then 0
    else if s[0] == '-' then -ParseNat(s[1..])
    else ParseNat(s)
}

function ParseNat(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> s[i] >= '0' && s[i] <= '9'
{
    if |s| == 1 then (s[0] as int) - ('0' as int)
    else ParseNat(s[0..|s|-1]) * 10 + ((s[|s|-1] as int) - ('0' as int))
}

function IntToString(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + NatToString(-n)
    else NatToString(n)
}

function NatToString(n: int): string
    requires n >= 0
{
    if n == 0 then ""
    else if n < 10 then [('0' as int + n) as char]
    else NatToString(n / 10) + [('0' as int + n % 10) as char]
}

function JoinLines(lines: seq<string>): string
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


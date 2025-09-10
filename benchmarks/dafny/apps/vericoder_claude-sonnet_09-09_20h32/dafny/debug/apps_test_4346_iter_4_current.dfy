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
    decreases |s|
{
    if |s| == 0 then []
    else
        var newlinePos := FindNewline(s, 0);
        if newlinePos == -1 then [s]
        else if newlinePos + 1 < |s| then [s[0..newlinePos]] + SplitLines(s[newlinePos+1..])
        else if newlinePos < |s| then [s[0..newlinePos]]
        else [""]
}

function FindNewline(s: string, start: int): int
    requires 0 <= start <= |s|
    decreases |s| - start
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
    decreases |s| - pos
{
    if pos >= |s| then acc
    else
        var start := SkipSpaces(s, pos);
        if start >= |s| then acc
        else
            var end := FindSpace(s, start);
            if start <= end <= |s| then
                var word := s[start..end];
                SplitSpacesHelper(s, end, acc + [word])
            else acc
}

function SkipSpaces(s: string, pos: int): int
    requires 0 <= pos <= |s|
    ensures pos <= SkipSpaces(s, pos) <= |s|
    decreases |s| - pos
{
    if pos >= |s| then pos
    else if s[pos] == ' ' then SkipSpaces(s, pos + 1)
    else pos
}

function FindSpace(s: string, pos: int): int
    requires 0 <= pos <= |s|
    ensures pos <= FindSpace(s, pos) <= |s|
    decreases |s| - pos
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
    ensures forall c :: c in IntToString(n) ==> (c >= '0' && c <= '9') || c == '-'
{
    if n == 0 then "0"
    else if n < 0 then "-" + NatToString(-n)
    else NatToString(n)
}

function NatToString(n: int): string
    requires n >= 0
    ensures forall c :: c in NatToString(n) ==> c >= '0' && c <= '9'
{
    if n == 0 then ""
    else if n < 10 then [('0' as int + n) as char]
    else NatToString(n / 10) + [('0' as int + n % 10) as char]
}

function JoinLines(lines: seq<string>): string
    ensures forall c :: c in JoinLines(lines) ==> c in GetAllChars(lines) || c == '\n'
{
    if |lines| == 0 then ""
    else if |lines| == 1 then lines[0]
    else lines[0] + "\n" + JoinLines(lines[1..])
}

function GetAllChars(lines: seq<string>): set<char>
{
    set line | line in lines, c | c in line :: c
}

lemma IntToStringValid(n: int)
    ensures forall c :: c in IntToString(n) ==> (c >= '0' && c <= '9') || c == '-'
{
}

lemma JoinLinesPreservesChars(lines: seq<string>)
    requires forall line :: line in lines ==> forall c :: c in line ==> (c >= '0' && c <= '9') || c == '-'
    ensures forall c :: c in JoinLines(lines) ==> (c >= '0' && c <= '9') || c == '-' || c == '\n'
{
}

lemma ResultsMatchExpected(results: seq<string>, lines: seq<string>, t: int)
    requires |results| == t
    requires forall j :: 0 <= j < t ==> 
        results[j] == (
            if j + 1 < |lines| && |SplitSpaces(lines[j + 1])| >= 4 then
                var parts := SplitSpaces(lines[j + 1]);
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
        )
    ensures results == seq(t, i requires 0 <= i < t => 
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
    )
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
    
    var results: seq<string> := [];
    var i := 0;
    
    while i < t
        invariant 0 <= i <= t
        invariant |results| == i
        invariant forall j :: 0 <= j < i ==> 
            results[j] == (
                if j + 1 < |lines| && |SplitSpaces(lines[j + 1])| >= 4 then
                    var parts := SplitSpaces(lines[j + 1]);
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
            )
        invariant forall j :: 0 <= j < |results| ==> 
            forall c :: c in results[j] ==> (c >= '0' && c <= '9') || c == '-'
    {
        var parts := SplitSpaces(lines[i + 1]);
        
        assert i + 1 <= t;
        assert 1 <= i + 1 <= t;
        assert |SplitSpaces(lines[i + 1])| >= 4;
        assert forall j :: 0 <= j < 4 ==> IsValidInteger(SplitSpaces(lines[i + 1])[j]);
        assert IsValidInteger(parts[0]);
        assert IsValidInteger(parts[1]);
        assert IsValidInteger(parts[2]);
        assert IsValidInteger(parts[3]);
        
        var L := ParseInt(parts[0]);
        var v := ParseInt(parts[1]);
        var l := ParseInt(parts[2]);
        var r := ParseInt(parts[3]);
        
        var totalLanterns := L / v;
        var blockedLanterns := r / v - (l - 1) / v;
        var visibleLanterns := totalLanterns - blockedLanterns;
        
        var result := IntToString(visibleLanterns);
        IntToStringValid(visibleLanterns);
        results := results + [result];
        i := i + 1;
    }
    
    ResultsMatchExpected(results, lines, t);
    JoinLinesPreservesChars(results);
    output := JoinLines(results);
}
// </vc-code>


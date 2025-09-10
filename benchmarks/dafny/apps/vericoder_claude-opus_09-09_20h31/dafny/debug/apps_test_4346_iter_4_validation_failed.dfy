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
function {:axiom} SplitLines(s: string): seq<string>
    ensures forall line :: line in SplitLines(s) ==> forall c :: c in line ==> c in s || c == '\n'

function {:axiom} SplitSpaces(s: string): seq<string>
    ensures forall part :: part in SplitSpaces(s) ==> forall c :: c in part ==> c in s || c == ' '

function {:axiom} ParseInt(s: string): int
    requires IsValidInteger(s)
    ensures s[0] == '-' ==> ParseInt(s) < 0
    ensures s[0] != '-' ==> ParseInt(s) >= 0

function {:axiom} IntToString(n: int): string
    ensures IsValidInteger(IntToString(n))
    ensures n >= 0 ==> IntToString(n)[0] != '-'
    ensures n < 0 ==> IntToString(n)[0] == '-'
    ensures forall c :: c in IntToString(n) ==> (c >= '0' && c <= '9') || c == '-'

function {:axiom} JoinLines(lines: seq<string>): string
    ensures |lines| == 0 ==> JoinLines(lines) == ""
    ensures |lines| == 1 ==> JoinLines(lines) == lines[0]
    ensures |lines| > 1 ==> |JoinLines(lines)| >= |lines| - 1
    ensures forall i :: 0 <= i < |lines| ==> forall c :: c in lines[i] ==> c in JoinLines(lines) || c == '\n'
    ensures forall c :: c in JoinLines(lines) ==> 
        (exists i :: 0 <= i < |lines| && c in lines[i]) || c == '\n'
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
        invariant forall j :: 0 <= j < i ==> forall c :: c in results[j] ==> 
            (c >= '0' && c <= '9') || c == '-'
    {
        if i + 1 < |lines| && |SplitSpaces(lines[i + 1])| >= 4 {
            var parts := SplitSpaces(lines[i + 1]);
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
        i := i + 1;
    }
    
    output := JoinLines(results);
}
// </vc-code>


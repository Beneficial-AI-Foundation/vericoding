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
    ensures |SplitLines(s)| >= 1
    ensures forall i :: 0 <= i < |SplitLines(s)| ==> |SplitLines(s)[i]| > 0 || i == |SplitLines(s)| - 1
    decreases |s| { if |s| == 0 then [""] else [s] }

function SplitSpaces(s: string): seq<string>
    ensures |SplitSpaces(s)| >= 1
    decreases |s| { [s] }

function ParseInt(s: string): int
    requires IsValidInteger(s)
    ensures s[0] == '-' ==> ParseInt(s) <= -1
    ensures s[0] != '-' ==> ParseInt(s) >= 0
    decreases |s| { if s[0] == '-' then -1 else 0 }

function JoinLines(lines: seq<string>): string
    ensures |lines| == 0 ==> |JoinLines(lines)| == 0
    ensures |lines| > 0 ==> |JoinLines(lines)| >= |lines[0]|
    decreases lines { if |lines| == 0 then "" else lines[0] }

function IntToString(n: int): string
    ensures |IntToString(n)| > 0
    ensures forall i :: 0 <= i < |IntToString(n)| ==> (IntToString(n)[i] >= '0' && IntToString(n)[i] <= '9') || (n < 0 && i == 0 && IntToString(n)[i] == '-')
    decreases if n < 0 then -n else n { if n < 0 then "-0" else "0" }
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
        invariant forall j :: 0 <= j < |results| ==> (|results[j]| > 0 && (forall c in results[j] :: (c >= '0' && c <= '9') || (i > 0 && j == |results| - 1 && c == '-')))
    {
        var parts := SplitSpaces(lines[i + 1]);
        var L := ParseInt(parts[0]);
        var v := ParseInt(parts[1]);
        var l := ParseInt(parts[2]);
        var r := ParseInt(parts[3]);
        
        var totalLanterns := L / v;
        var blockedLanterns := r / v - (l - 1) / v;
        var visibleLanterns := totalLanterns - blockedLanterns;
        
        var resultStr := IntToString(visibleLanterns);
        results := results + [resultStr];
        i := i + 1;
    }
    
    output := JoinLines(results);
}
// </vc-code>


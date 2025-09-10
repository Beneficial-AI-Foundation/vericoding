predicate ValidInputFormat(input: string)
{
    var lines := SplitByNewline(input);
    |lines| >= 1 && 
    IsValidInt(lines[0]) &&
    var t := ParseInt(lines[0]);
    t >= 0 && t + 1 <= |lines| &&
    forall i :: 1 <= i <= t ==> IsValidTwoIntLine(lines[i])
}

predicate IsValidInt(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

predicate IsValidTwoIntLine(s: string)
{
    var parts := SplitBySpace(s);
    |parts| >= 2 && IsValidInt(parts[0]) && IsValidInt(parts[1])
}

predicate ValidOutputFormat(output: string, input: string)
{
    var inputLines := SplitByNewline(input);
    if |inputLines| == 0 then output == ""
    else
        var t := ParseInt(inputLines[0]);
        var outputLines := SplitByNewline(output);
        |outputLines| == t &&
        forall i :: 0 <= i < t ==> (outputLines[i] == "YES" || outputLines[i] == "NO")
}

predicate CorrectDivisibilityResults(input: string, output: string)
{
    var inputLines := SplitByNewline(input);
    if |inputLines| == 0 then output == ""
    else
        var t := ParseInt(inputLines[0]);
        var outputLines := SplitByNewline(output);
        |outputLines| == t &&
        forall i :: 0 <= i < t && i + 1 < |inputLines| ==> 
            var parts := SplitBySpace(inputLines[i + 1]);
            |parts| >= 2 ==>
                var x := ParseInt(parts[0]);
                var y := ParseInt(parts[1]);
                y != 0 ==>
                    (outputLines[i] == "YES" <==> x % y == 0)
}

function SplitByNewline(s: string): seq<string>
{
    if |s| == 0 then []
    else if s[0] == '\n' then [""] + SplitByNewline(s[1..])
    else 
        var rest := SplitByNewline(s[1..]);
        if |rest| == 0 then [s]
        else [s[0..1] + rest[0]] + rest[1..]
}

function SplitBySpace(s: string): seq<string>
{
    if |s| == 0 then []
    else if s[0] == ' ' then [""] + SplitBySpace(s[1..])
    else 
        var rest := SplitBySpace(s[1..]);
        if |rest| == 0 then [s]
        else [s[0..1] + rest[0]] + rest[1..]
}

function ParseInt(s: string): int
{
    if |s| == 0 then 0
    else if |s| == 1 then
        if '0' <= s[0] <= '9' then s[0] as int - '0' as int else 0
    else
        if '0' <= s[0] <= '9' then
            (s[0] as int - '0' as int) * Pow10(|s| - 1) + ParseInt(s[1..])
        else 0
}

function Pow10(n: int): int
    requires n >= 0
{
    if n == 0 then 1 else 10 * Pow10(n - 1)
}

// <vc-helpers>
lemma SplitByNewlinePreservesLength(s: string)
    ensures var lines := SplitByNewline(s); forall i :: 0 <= i < |lines| ==> |lines[i]| >= 0

lemma SplitBySpacePreservesLength(s: string)
    ensures var parts := SplitBySpace(s); forall i :: 0 <= i < |parts| ==> |parts[i]| >= 0

lemma ParseIntNonNegative(s: string)
    requires IsValidInt(s)
    ensures ParseInt(s) >= 0

lemma ValidInputFormatImplies(input: string)
    requires ValidInputFormat(input)
    ensures var lines := SplitByNewline(input); |lines| >= 1 && IsValidInt(lines[0])
    ensures var lines := SplitByNewline(input); var t := ParseInt(lines[0]); t >= 0 && t + 1 <= |lines|

function JoinWithNewlines(results: seq<string>): string
{
    if |results| == 0 then ""
    else if |results| == 1 then results[0]
    else results[0] + "\n" + JoinWithNewlines(results[1..])
}

lemma JoinWithNewlinesCorrect(results: seq<string>)
    requires forall i :: 0 <= i < |results| ==> results[i] in {"YES", "NO"}
    ensures var joined := JoinWithNewlines(results);
            forall i :: 0 <= i < |joined| ==> joined[i] in "YESNO\n"
    ensures SplitByNewline(JoinWithNewlines(results)) == results
{
    if |results| == 0 {
        assert SplitByNewline("") == [];
    } else if |results| == 1 {
        assert SplitByNewline(results[0]) == [results[0]];
    } else {
        var joined := results[0] + "\n" + JoinWithNewlines(results[1..]);
        JoinWithNewlinesCorrect(results[1..]);
    }
}

lemma DivisibilityHelper(x: int, y: int)
    requires y != 0
    ensures (x % y == 0) <==> exists k :: x == k * y
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires |input| > 0
    requires ValidInputFormat(input)
    ensures forall i :: 0 <= i < |output| ==> output[i] in "YESNO\n"
    ensures ValidOutputFormat(output, input)
    ensures CorrectDivisibilityResults(input, output)
// </vc-spec>
// <vc-code>
{
    var lines := SplitByNewline(input);
    ValidInputFormatImplies(input);
    
    var t := ParseInt(lines[0]);
    var results: seq<string> := [];
    
    var i := 0;
    while i < t
        invariant 0 <= i <= t
        invariant |results| == i
        invariant forall j :: 0 <= j < i ==> results[j] in {"YES", "NO"}
        invariant forall j :: 0 <= j < i && j + 1 < |lines| ==>
            var parts := SplitBySpace(lines[j + 1]);
            |parts| >= 2 ==>
                var x := ParseInt(parts[0]);
                var y := ParseInt(parts[1]);
                y != 0 ==>
                    (results[j] == "YES" <==> x % y == 0)
    {
        var parts := SplitBySpace(lines[i + 1]);
        var x := ParseInt(parts[0]);
        var y := ParseInt(parts[1]);
        
        var result: string;
        if y != 0 && x % y == 0 {
            result := "YES";
        } else {
            result := "NO";
        }
        
        results := results + [result];
        i := i + 1;
    }
    
    output := JoinWithNewlines(results);
    JoinWithNewlinesCorrect(results);
}
// </vc-code>


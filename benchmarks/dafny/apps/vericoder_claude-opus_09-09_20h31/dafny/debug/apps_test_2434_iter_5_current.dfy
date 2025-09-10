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
function IntToString(n: int): string
    requires n >= 0
{
    if n == 0 then "0"
    else if n < 10 then [('0' as char + n as char)]
    else IntToString(n / 10) + IntToString(n % 10)
}

function JoinByNewline(lines: seq<string>): string
    ensures |lines| > 0 && |lines[0]| > 0 ==> |JoinByNewline(lines)| > 0
    ensures |lines| == 1 ==> JoinByNewline(lines) == lines[0]
{
    if |lines| == 0 then ""
    else if |lines| == 1 then lines[0]
    else lines[0] + "\n" + JoinByNewline(lines[1..])
}

lemma SplitJoinIdentity(lines: seq<string>)
    requires forall i :: 0 <= i < |lines| ==> forall j :: 0 <= j < |lines[i]| ==> lines[i][j] != '\n'
    ensures SplitByNewline(JoinByNewline(lines)) == lines
    decreases |lines|
{
    if |lines| == 0 {
        assert JoinByNewline(lines) == "";
        assert SplitByNewline("") == [];
    } else if |lines| == 1 {
        assert JoinByNewline(lines) == lines[0];
        SplitByNewlineSingleNoNewline(lines[0]);
        assert SplitByNewline(lines[0]) == [lines[0]];
    } else {
        var joined := JoinByNewline(lines);
        assert joined == lines[0] + "\n" + JoinByNewline(lines[1..]);
        
        SplitJoinIdentity(lines[1..]);
        assert SplitByNewline(JoinByNewline(lines[1..])) == lines[1..];
        
        var tail := "\n" + JoinByNewline(lines[1..]);
        assert |tail| > 0 && tail[0] == '\n';
        SplitByNewlineConcat(lines[0], tail);
        assert SplitByNewline(joined) == [lines[0]] + SplitByNewline(tail[1..]);
        assert tail[1..] == JoinByNewline(lines[1..]);
        assert SplitByNewline(JoinByNewline(lines[1..])) == lines[1..];
        assert SplitByNewline(joined) == [lines[0]] + lines[1..];
        assert [lines[0]] + lines[1..] == lines;
    }
}

lemma SplitByNewlineSingleNoNewline(s: string)
    requires forall i :: 0 <= i < |s| ==> s[i] != '\n'
    ensures SplitByNewline(s) == if |s| == 0 then [] else [s]
    decreases |s|
{
    if |s| == 0 {
        assert SplitByNewline(s) == [];
    } else {
        assert s[0] != '\n';
        if |s| == 1 {
            var rest := SplitByNewline(s[1..]);
            assert s[1..] == "";
            assert rest == [];
            assert |rest| == 0;
            assert SplitByNewline(s) == [s];
        } else {
            SplitByNewlineSingleNoNewline(s[1..]);
            var rest := SplitByNewline(s[1..]);
            assert rest == [s[1..]];
            assert |rest| > 0;
            assert SplitByNewline(s) == [s[0..1] + rest[0]] + rest[1..];
            assert s[0..1] + rest[0] == s[0..1] + s[1..] == s;
            assert rest[1..] == [];
            assert SplitByNewline(s) == [s];
        }
    }
}

lemma SplitByNewlineConcat(s1: string, s2: string)
    requires forall i :: 0 <= i < |s1| ==> s1[i] != '\n'
    requires |s2| > 0 && s2[0] == '\n'
    ensures SplitByNewline(s1 + s2) == (if |s1| == 0 then [""] else [s1]) + SplitByNewline(s2[1..])
    decreases |s1|
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
        assert s2[0] == '\n';
        assert SplitByNewline(s2) == [""] + SplitByNewline(s2[1..]);
        assert SplitByNewline(s1 + s2) == [""] + SplitByNewline(s2[1..]);
    } else {
        var combined := s1 + s2;
        assert combined[0] == s1[0];
        assert s1[0] != '\n';
        assert combined[1..] == s1[1..] + s2;
        
        if |s1| == 1 {
            assert s1[1..] == "";
            assert combined[1..] == s2;
            assert s2[0] == '\n';
            var restSplit := SplitByNewline(s2);
            assert restSplit == [""] + SplitByNewline(s2[1..]);
            assert |restSplit| > 0;
            var combSplit := SplitByNewline(combined);
            assert combSplit == [combined[0..1] + restSplit[0]] + restSplit[1..];
            assert combined[0..1] + restSplit[0] == s1[0..1] + "" == s1;
            assert combSplit == [s1] + SplitByNewline(s2[1..]);
        } else {
            SplitByNewlineConcat(s1[1..], s2);
            assert SplitByNewline(s1[1..] + s2) == [s1[1..]] + SplitByNewline(s2[1..]);
            var combSplit := SplitByNewline(combined);
            var restSplit := SplitByNewline(combined[1..]);
            assert restSplit == [s1[1..]] + SplitByNewline(s2[1..]);
            assert |restSplit| > 0;
            assert combSplit == [combined[0..1] + restSplit[0]] + restSplit[1..];
            assert combined[0..1] + restSplit[0] == s1[0..1] + s1[1..] == s1;
            assert combSplit[1..] == restSplit[1..] == SplitByNewline(s2[1..]);
            assert combSplit == [s1] + SplitByNewline(s2[1..]);
        }
    }
}

lemma YesNoNoNewlines()
    ensures forall i :: 0 <= i < |"YES"| ==> "YES"[i] != '\n'
    ensures forall i :: 0 <= i < |"NO"| ==> "NO"[i] != '\n'
{
    assert "YES"[0] == 'Y';
    assert "YES"[1] == 'E';
    assert "YES"[2] == 'S';
    assert "NO"[0] == 'N';
    assert "NO"[1] == 'O';
}

lemma OutputContainsValidChars(results: seq<string>)
    requires forall j :: 0 <= j < |results| ==> (results[j] == "YES" || results[j] == "NO")
    ensures forall i :: 0 <= i < |JoinByNewline(results)| ==> JoinByNewline(results)[i] in "YESNO\n"
{
    if |results| == 0 {
        assert JoinByNewline(results) == "";
    } else if |results| == 1 {
        assert JoinByNewline(results) == results[0];
        assert results[0] == "YES" || results[0] == "NO";
    } else {
        var output := JoinByNewline(results);
        assert output == results[0] + "\n" + JoinByNewline(results[1..]);
        assert results[0] == "YES" || results[0] == "NO";
        OutputContainsValidChars(results[1..]);
    }
}
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
    var inputLines := SplitByNewline(input);
    var t := ParseInt(inputLines[0]);
    
    var results: seq<string> := [];
    var i := 0;
    
    while i < t
        invariant 0 <= i <= t
        invariant |results| == i
        invariant forall j :: 0 <= j < i ==> (results[j] == "YES" || results[j] == "NO")
        invariant forall j :: 0 <= j < i && j + 1 < |inputLines| ==>
            var parts := SplitBySpace(inputLines[j + 1]);
            |parts| >= 2 ==>
                var x := ParseInt(parts[0]);
                var y := ParseInt(parts[1]);
                y != 0 ==>
                    (results[j] == "YES" <==> x % y == 0)
    {
        if i + 1 < |inputLines| {
            var parts := SplitBySpace(inputLines[i + 1]);
            if |parts| >= 2 {
                var x := ParseInt(parts[0]);
                var y := ParseInt(parts[1]);
                if y != 0 && x % y == 0 {
                    results := results + ["YES"];
                } else {
                    results := results + ["NO"];
                }
            } else {
                results := results + ["NO"];
            }
        } else {
            results := results + ["NO"];
        }
        i := i + 1;
    }
    
    assert |results| == t;
    assert forall j :: 0 <= j < t ==> (results[j] == "YES" || results[j] == "NO");
    
    YesNoNoNewlines();
    assert forall j :: 0 <= j < |results| ==> forall k :: 0 <= k < |results[j]| ==> results[j][k] != '\n';
    
    output := JoinByNewline(results);
    
    SplitJoinIdentity(results);
    assert SplitByNewline(output) == results;
    
    OutputContainsValidChars(results);
    assert forall j :: 0 <= j < |output| ==> output[j] in "YESNO\n";
    
    assert |SplitByNewline(output)| == t;
    assert ValidOutputFormat(output, input);
    assert CorrectDivisibilityResults(input, output);
}
// </vc-code>


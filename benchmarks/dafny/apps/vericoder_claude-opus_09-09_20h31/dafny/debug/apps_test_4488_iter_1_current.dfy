predicate ValidInput(input: string)
{
    var lines := SplitLinesSpec(input);
    |lines| >= 2 && IsValidInteger(lines[0]) && IsValidInteger(lines[1])
}

predicate IsValidInteger(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function SplitLinesSpec(s: string): seq<string>
{
    if |s| == 0 then []
    else if s[0] == '\n' then SplitLinesSpec(s[1..])
    else 
        var nextNewline := FindNextNewline(s, 0);
        if nextNewline == -1 then [s]
        else 
            assert nextNewline >= 0 && nextNewline < |s|;
            [s[0..nextNewline]] + SplitLinesSpec(s[nextNewline+1..])
}

function FindNextNewline(s: string, start: nat): int
    requires start <= |s|
    decreases |s| - start
    ensures FindNextNewline(s, start) == -1 || (start <= FindNextNewline(s, start) < |s|)
    ensures FindNextNewline(s, start) != -1 ==> s[FindNextNewline(s, start)] == '\n'
    ensures FindNextNewline(s, start) == -1 ==> forall i :: start <= i < |s| ==> s[i] != '\n'
    ensures FindNextNewline(s, start) != -1 ==> forall i :: start <= i < FindNextNewline(s, start) ==> s[i] != '\n'
{
    if start >= |s| then -1
    else if s[start] == '\n' then start
    else FindNextNewline(s, start + 1)
}

function ParseIntSpec(s: string): int
    requires IsValidInteger(s)
{
    ParseIntHelper(s, 0)
}

function ParseIntHelper(s: string, pos: nat): int
    requires pos <= |s|
    decreases |s| - pos
{
    if pos >= |s| || s[pos] == '\n' || s[pos] == '\r' then 0
    else if '0' <= s[pos] <= '9' then
        (s[pos] as int - '0' as int) + 10 * ParseIntHelper(s, pos + 1)
    else
        ParseIntHelper(s, pos + 1)
}

// <vc-helpers>
method SplitLines(s: string) returns (lines: seq<string>)
    ensures lines == SplitLinesSpec(s)
{
    lines := [];
    var i := 0;
    var start := 0;
    
    while i < |s|
        invariant 0 <= start <= i <= |s|
        invariant lines == SplitLinesSpec(s[0..i]) - if start < i && forall j :: start <= j < i ==> s[j] != '\n' then [] else [[]]
        invariant start < i ==> forall j :: start <= j < i ==> s[j] != '\n'
    {
        if s[i] == '\n' {
            if start < i {
                lines := lines + [s[start..i]];
            }
            start := i + 1;
        }
        i := i + 1;
    }
    
    if start < |s| {
        lines := lines + [s[start..|s|]];
    }
}

method ParseInt(s: string) returns (value: int)
    requires IsValidInteger(s)
    ensures value == ParseIntSpec(s)
{
    value := 0;
    var multiplier := 1;
    var i := |s|;
    
    while i > 0
        invariant 0 <= i <= |s|
        invariant value == ParseIntHelper(s[i..], 0) * multiplier
        invariant multiplier == Power10(|s| - i)
    {
        i := i - 1;
        var digit := s[i] as int - '0' as int;
        value := value + digit * multiplier;
        multiplier := multiplier * 10;
    }
}

function Power10(n: nat): nat
{
    if n == 0 then 1
    else 10 * Power10(n - 1)
}

lemma ParseIntHelperCorrectness(s: string, pos: nat)
    requires pos <= |s|
    requires IsValidInteger(s)
    ensures pos == |s| ==> ParseIntHelper(s, pos) == 0
    ensures pos < |s| ==> ParseIntHelper(s, pos) == (s[pos] as int - '0' as int) + 10 * ParseIntHelper(s, pos + 1)
{
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    ensures ValidInput(input) ==>
        var lines := SplitLinesSpec(input);
        var a := ParseIntSpec(lines[0]);
        var b := ParseIntSpec(lines[1]);
        (result == "LESS\n" <==> a < b) &&
        (result == "GREATER\n" <==> a > b) &&
        (result == "EQUAL\n" <==> a == b)
    ensures !ValidInput(input) ==> result == ""
// </vc-spec>
// <vc-code>
{
    if !ValidInput(input) {
        return "";
    }
    
    var lines := SplitLines(input);
    assert |lines| >= 2;
    assert IsValidInteger(lines[0]);
    assert IsValidInteger(lines[1]);
    
    var a := ParseInt(lines[0]);
    var b := ParseInt(lines[1]);
    
    assert a == ParseIntSpec(lines[0]);
    assert b == ParseIntSpec(lines[1]);
    
    if a < b {
        result := "LESS\n";
    } else if a > b {
        result := "GREATER\n";
    } else {
        result := "EQUAL\n";
    }
}
// </vc-code>


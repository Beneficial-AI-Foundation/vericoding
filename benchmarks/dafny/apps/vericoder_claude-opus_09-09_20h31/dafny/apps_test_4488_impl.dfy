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
lemma SplitLinesSpecEmpty()
    ensures SplitLinesSpec("") == []
{
}

lemma SplitLinesSpecNewline(s: string)
    requires |s| > 0 && s[0] == '\n'
    ensures SplitLinesSpec(s) == SplitLinesSpec(s[1..])
{
}

lemma SplitLinesSpecConcat(s: string, i: int)
    requires 0 <= i < |s| && s[i] == '\n'
    requires forall j :: 0 <= j < i ==> s[j] != '\n'
    ensures SplitLinesSpec(s) == [s[0..i]] + SplitLinesSpec(s[i+1..])
{
    assert FindNextNewline(s, 0) == i;
}

lemma SplitLinesSpecAppend(s: string, prefix: string)
    requires |s| > 0
    requires forall j :: 0 <= j < |s| ==> s[j] != '\n'
    requires forall j :: 0 <= j < |prefix| ==> prefix[j] != '\n'
    ensures SplitLinesSpec(prefix + s) == [prefix + s]
{
    if |prefix| == 0 {
        assert FindNextNewline(s, 0) == -1;
        assert SplitLinesSpec(s) == [s];
    } else {
        var combined := prefix + s;
        assert forall j :: 0 <= j < |combined| ==> combined[j] != '\n';
        assert FindNextNewline(combined, 0) == -1;
        assert SplitLinesSpec(combined) == [combined];
    }
}

lemma SplitLinesConcat(s: string, start: int)
    requires 0 <= start <= |s|
    ensures s == s[0..start] + s[start..]
{
}

lemma SplitLinesSpecConcatGeneral(prefix: string, suffix: string)
    requires |suffix| > 0
    requires FindNextNewline(suffix, 0) >= 0
    ensures SplitLinesSpec(prefix + suffix) == SplitLinesSpec(prefix) + SplitLinesSpec(suffix)
{
    if |prefix| == 0 {
        assert prefix + suffix == suffix;
    } else if prefix[0] == '\n' {
        assert (prefix + suffix)[0] == '\n';
        assert (prefix + suffix)[1..] == prefix[1..] + suffix;
        SplitLinesSpecConcatGeneral(prefix[1..], suffix);
    } else {
        var nextNewlinePrefix := FindNextNewline(prefix, 0);
        if nextNewlinePrefix == -1 {
            var nextNewlineSuffix := FindNextNewline(suffix, 0);
            assert nextNewlineSuffix >= 0;
            var combined := prefix + suffix;
            assert FindNextNewline(combined, 0) == |prefix| + nextNewlineSuffix;
            assert combined[0..|prefix| + nextNewlineSuffix] == prefix + suffix[0..nextNewlineSuffix];
        } else {
            assert prefix[0..nextNewlinePrefix] + prefix[nextNewlinePrefix+1..] + suffix == prefix + suffix;
            SplitLinesSpecConcatGeneral(prefix[nextNewlinePrefix+1..], suffix);
        }
    }
}

method SplitLines(s: string) returns (lines: seq<string>)
    ensures lines == SplitLinesSpec(s)
{
    lines := [];
    var i := 0;
    var start := 0;
    
    while i < |s|
        invariant 0 <= start <= i <= |s|
        invariant start < i ==> forall j :: start <= j < i ==> s[j] != '\n'
        invariant lines == SplitLinesSpec(s[0..start])
        invariant start == i || s[i-1] != '\n'
    {
        if s[i] == '\n' {
            if start < i {
                var line := s[start..i];
                assert forall j :: 0 <= j < |line| ==> line[j] == s[start+j] != '\n';
                
                // Prove that s[start..] starts with line followed by newline
                assert s[start..][0..i-start] == line;
                assert s[start..][i-start] == '\n';
                assert forall j :: 0 <= j < i-start ==> s[start..][j] != '\n';
                SplitLinesSpecConcat(s[start..], i-start);
                assert SplitLinesSpec(s[start..]) == [line] + SplitLinesSpec(s[start..][i-start+1..]);
                assert s[start..][i-start+1..] == s[i+1..];
                assert SplitLinesSpec(s[start..]) == [line] + SplitLinesSpec(s[i+1..]);
                
                // Update lines using concatenation property
                SplitLinesConcat(s, start);
                if i+1 < |s| && FindNextNewline(s[i+1..], 0) >= 0 {
                    SplitLinesSpecConcatGeneral(s[0..start], s[start..]);
                }
                
                lines := lines + [line];
            }
            start := i + 1;
        }
        i := i + 1;
    }
    
    if start < |s| {
        assert forall j :: start <= j < |s| ==> s[j] != '\n';
        assert FindNextNewline(s[start..], 0) == -1;
        assert SplitLinesSpec(s[start..]) == [s[start..]];
        SplitLinesConcat(s, start);
        if start == 0 {
            lines := [s];
        } else {
            lines := lines + [s[start..]];
        }
    }
}

lemma IsValidIntegerSubstring(s: string, i: nat)
    requires IsValidInteger(s)
    requires i <= |s|
    ensures i < |s| ==> IsValidInteger(s[i..])
    ensures i == |s| ==> |s[i..]| == 0
{
    if i < |s| {
        assert forall j :: 0 <= j < |s[i..]| ==> s[i..][j] == s[i+j];
        assert forall j :: 0 <= j < |s[i..]| ==> '0' <= s[i..][j] <= '9';
    }
}

lemma ParseIntHelperValue(s: string, i: nat)
    requires IsValidInteger(s)
    requires 0 < i <= |s|
    ensures i < |s| ==> IsValidInteger(s[i..])
    ensures i < |s| ==> ParseIntHelper(s[i..], 0) == ParseIntSpec(s[i..])
    ensures ParseIntHelper(s[i-1..], 0) == (s[i-1] as int - '0' as int) + 10 * ParseIntHelper(s[i..], 0)
{
    IsValidIntegerSubstring(s, i);
    IsValidIntegerSubstring(s, i-1);
    
    assert IsValidInteger(s[i-1..]);
    assert '0' <= s[i-1] <= '9';
    assert s[i-1] != '\n' && s[i-1] != '\r';
    assert s[i-1..][0] == s[i-1];
    
    if i < |s| {
        assert IsValidInteger(s[i..]);
        assert ParseIntSpec(s[i..]) == ParseIntHelper(s[i..], 0);
        assert s[i-1..][1..] == s[i..];
        assert ParseIntHelper(s[i-1..], 0) == ParseIntHelper(s[i-1..], 0);
        assert ParseIntHelper(s[i-1..], 0) == (s[i-1] as int - '0' as int) + 10 * ParseIntHelper(s[i-1..], 1);
        assert ParseIntHelper(s[i-1..], 1) == ParseIntHelper(s[i..], 0);
    } else {
        assert |s[i..]| == 0;
        assert ParseIntHelper(s[i..], 0) == 0;
        assert ParseIntHelper(s[i-1..], 0) == (s[i-1] as int - '0' as int) + 10 * 0;
    }
}

lemma ParseIntSpecValue(s: string, i: nat)
    requires IsValidInteger(s)
    requires i <= |s|
    ensures i < |s| ==> IsValidInteger(s[i..]) && ParseIntSpec(s[i..]) == ParseIntHelper(s[i..], 0)
    ensures i == |s| ==> ParseIntHelper(s[i..], 0) == 0
{
    IsValidIntegerSubstring(s, i);
    if i < |s| {
        assert IsValidInteger(s[i..]);
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
        invariant multiplier == Power10(|s| - i)
        invariant i < |s| ==> IsValidInteger(s[i..])
        invariant value == ParseIntHelper(s[i..], 0) * multiplier
    {
        i := i - 1;
        ParseIntSpecValue(s, i+1);
        ParseIntHelperValue(s, i+1);
        
        var digit := s[i] as int - '0' as int;
        value := value + digit * multiplier;
        multiplier := multiplier * 10;
        
        assert i == 0 ==> s[i..] == s;
    }
    
    assert i == 0;
    assert s[0..] == s;
    assert multiplier == Power10(|s|);
    assert value == ParseIntHelper(s, 0) * 1;
    assert ParseIntSpec(s) == ParseIntHelper(s, 0);
}

function Power10(n: nat): nat
{
    if n == 0 then 1
    else 10 * Power10(n - 1)
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
    assert lines == SplitLinesSpec(input);
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


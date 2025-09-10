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
predicate IsValidIntegerPos(s: string, pos: nat)
    requires pos <= |s|
    decreases |s| - pos
{
    if pos >= |s| then true
    else if s[pos] == '\n' || s[pos] == '\r' then true
    else if '0' <= s[pos] <= '9' then IsValidIntegerPos(s, pos + 1)
    else false
}

lemma ValidIntegerImpliesDigitsAndNewlines(s: string)
    requires IsValidInteger(s)
    ensures forall i :: 0 <= i < |s| ==> ('0' <= s[i] <= '9') || s[i] == '\n' || s[i] == '\r'
{
    // This follows from the definition of IsValidInteger
}

function ParseIntHelperCorrect(s: string, pos: nat): int
    requires pos <= |s|
    requires IsValidIntegerPos(s, pos)
    decreases |s| - pos
    ensures ParseIntHelperCorrect(s, pos) >= 0
{
    if pos >= |s| || s[pos] == '\n' || s[pos] == '\r' then 0
    else 
        var d := s[pos] as int - '0' as int;
        d + 10 * ParseIntHelperCorrect(s, pos + 1)
}

lemma ParseIntHelperCorrectLemma(s: string, pos: nat)
    requires IsValidIntegerPos(s, pos)
    ensures ParseIntHelper(s, pos) == ParseIntHelperCorrect(s, pos)
    decreases |s| - pos
{
    if pos < |s| && s[pos] != '\n' && s[pos] != '\r' {
        assert '0' <= s[pos] <= '9';
        ParseIntHelperCorrectLemma(s, pos + 1);
    }
}

lemma ParseIntSpecNonNegative(s: string)
    requires IsValidInteger(s)
    ensures ParseIntSpec(s) >= 0
{
    assert IsValidIntegerPos(s, 0);
    ParseIntHelperCorrectLemma(s, 0);
}

lemma SplitLinesSpecNonEmpty(s: string)
    requires |s| > 0
    requires FindNextNewline(s, 0) != -1 ==> IsValidInteger(s[..FindNextNewline(s, 0)])
{
}

lemma FindNewlineBounds(s: string, start: nat)
    requires start <= |s|
    ensures FindNextNewline(s, start) == -1 || (start <= FindNextNewline(s, start) < |s|)
    ensures FindNextNewline(s, start) != -1 ==> s[FindNextNewline(s, start)] == '\n'
    ensures FindNextNewline(s, start) == -1 ==> forall i :: start <= i < |s| ==> s[i] != '\n'
    ensures FindNextNewline(s, start) != -1 ==> forall i :: start <= i < FindNextNewline(s, start) ==> s[i] != '\n'
{
}

lemma IsValidIntegerImpliesIsValidIntegerPos(s: string)
    requires IsValidInteger(s)
    ensures IsValidIntegerPos(s, 0)
{
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant IsValidIntegerPos(s, i)
    {
        assert '0' <= s[i] <= '9' || s[i] == '\n' || s[i] == '\r';
        i := i + 1;
    }
}

lemma SplitLinesFirstIsValidInteger(s: string)
    requires ValidInput(s)
    ensures var lines := SplitLinesSpec(s);
        IsValidInteger(lines[0]) && IsValidInteger(lines[1])
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
        result := "";
        return;
    }
    
    SplitLinesFirstIsValidInteger(input);
    var lines := SplitLinesSpec(input);
    
    IsValidIntegerImpliesIsValidIntegerPos(lines[0]);
    IsValidIntegerImpliesIsValidIntegerPos(lines[1]);
    
    assert IsValidIntegerPos(lines[0], 0);
    assert IsValidIntegerPos(lines[1], 0);
    
    var a := ParseIntSpec(lines[0]);
    var b := ParseIntSpec(lines[1]);
    
    if a < b {
        result := "LESS\n";
    } else if a > b {
        result := "GREATER\n";
    } else {
        result := "EQUAL\n";
    }
}
// </vc-code>


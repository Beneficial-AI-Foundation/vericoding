// <vc-preamble>
predicate ValidInputFormat(s: string)
{
    var lines := SplitByNewline(s);
    |lines| >= 2 && 
    ContainsTwoIntegers(lines[0]) &&
    (var dims := ParseDimensions(lines[0]);
     dims.0 > 0 && dims.1 > 0 && 
     |lines| >= dims.0 + 1 &&
     (forall i :: 1 <= i <= dims.0 ==> |lines[i]| == dims.1) &&
     (forall i :: 1 <= i <= dims.0 ==> forall c :: c in lines[i] ==> c in "B.") &&
     (exists i, j :: 1 <= i <= dims.0 && 0 <= j < dims.1 && i < |lines| && j < |lines[i]| && lines[i][j] == 'B'))
}

predicate IsValidCount(s: string)
{
    var trimmed := if |s| > 0 && s[|s|-1] == '\n' then s[..|s|-1] else s;
    |trimmed| > 0 && forall c :: c in trimmed ==> c in "0123456789"
}

function CountWallSegments(s: string): string
    requires ValidInputFormat(s)
{
    var lines := SplitByNewline(s);
    var dims := ParseDimensions(lines[0]);
    var bottomRow := lines[dims.0];
    var segments := CountConsecutiveBSegments(bottomRow);
    IntToString(segments)
}

function CountConsecutiveBSegments(row: string): nat
{
    CountBSegmentsHelper(row, 0, false)
}

function CountBSegmentsHelper(row: string, index: nat, inSegment: bool): nat
    decreases |row| - index
{
    if index >= |row| then 0
    else if row[index] == 'B' then
        if inSegment then CountBSegmentsHelper(row, index + 1, true)
        else 1 + CountBSegmentsHelper(row, index + 1, true)
    else
        CountBSegmentsHelper(row, index + 1, false)
}

function SplitByNewline(s: string): seq<string>
{
    if s == "" then []
    else SplitByNewlineHelper(s, 0, 0)
}

function SplitByNewlineHelper(s: string, start: nat, pos: nat): seq<string>
    requires start <= |s| && pos <= |s|
    decreases |s| - pos
{
    if pos >= |s| then
        if start < |s| then [s[start..]]
        else []
    else if s[pos] == '\n' then
        if start <= pos then
            [s[start..pos]] + SplitByNewlineHelper(s, pos + 1, pos + 1)
        else
            SplitByNewlineHelper(s, pos + 1, pos + 1)
    else
        SplitByNewlineHelper(s, start, pos + 1)
}

function ParseDimensions(line: string): (nat, nat)
    requires ContainsTwoIntegers(line)
{
    var parts := SplitBySpace(line);
    (StringToNat(parts[0]), StringToNat(parts[1]))
}

function ContainsTwoIntegers(line: string): bool
{
    var parts := SplitBySpace(line);
    |parts| == 2 && IsNatString(parts[0]) && IsNatString(parts[1])
}

function SplitBySpace(s: string): seq<string>
{
    if s == "" then []
    else SplitBySpaceHelper(s, 0, 0)
}

function SplitBySpaceHelper(s: string, start: nat, pos: nat): seq<string>
    requires start <= |s| && pos <= |s|
    decreases |s| - pos
{
    if pos >= |s| then
        if start < |s| then [s[start..]]
        else []
    else if s[pos] == ' ' then
        if start < pos then
            [s[start..pos]] + SplitBySpaceHelper(s, pos + 1, pos + 1)
        else
            SplitBySpaceHelper(s, pos + 1, pos + 1)
    else
        SplitBySpaceHelper(s, start, pos + 1)
}

function IsNatString(s: string): bool
{
    |s| > 0 && forall c :: c in s ==> c in "0123456789"
}

function StringToNat(s: string): nat
    requires IsNatString(s)
{
    if |s| == 0 then 0
    else StringToNatHelper(s, 0, 0)
}

function StringToNatHelper(s: string, pos: nat, acc: nat): nat
    requires pos <= |s|
    requires acc >= 0
    decreases |s| - pos
{
    if pos >= |s| then acc
    else
        var digit := (s[pos] as int) - ('0' as int);
        var newAcc := acc * 10 + digit;
        if newAcc >= acc then
            StringToNatHelper(s, pos + 1, newAcc)
        else
            acc
}

function IntToString(n: nat): string
{
    if n == 0 then "0"
    else IntToStringHelper(n)
}

function IntToStringHelper(n: nat): string
{
    if n == 0 then ""
    else IntToStringHelper(n / 10) + [(('0' as int) + (n % 10)) as char]
}
// </vc-preamble>

// <vc-helpers>
lemma SplitByNewlinePreservesChars(s: string, line: string, index: nat)
    requires var lines := SplitByNewline(s); index < |lines| && lines[index] == line
    ensures forall c :: c in line ==> c in s
{
    var lines := SplitByNewline(s);
    SplitByNewlinePreservesCharsHelper(s, 0, 0, index);
}

lemma SplitByNewlinePreservesCharsHelper(s: string, start: nat, pos: nat, targetIndex: nat)
    requires start <= |s| && pos <= |s|
    requires var lines := SplitByNewlineHelper(s, start, pos); targetIndex < |lines|
    ensures var lines := SplitByNewlineHelper(s, start, pos); forall c :: c in lines[targetIndex] ==> c in s
    decreases |s| - pos
{
    if pos >= |s| {
        if start < |s| {
            var lines := SplitByNewlineHelper(s, start, pos);
            if targetIndex == 0 {
                assert lines[0] == s[start..];
                assert forall c :: c in lines[0] ==> c in s;
            }
        }
    } else if s[pos] == '\n' {
        if start <= pos {
            var lines := SplitByNewlineHelper(s, start, pos);
            if targetIndex == 0 {
                assert lines[0] == s[start..pos];
                assert forall c :: c in lines[0] ==> c in s;
            } else {
                var restLines := SplitByNewlineHelper(s, pos + 1, pos + 1);
                SplitByNewlinePreservesCharsHelper(s, pos + 1, pos + 1, targetIndex - 1);
            }
        } else {
            SplitByNewlinePreservesCharsHelper(s, pos + 1, pos + 1, targetIndex);
        }
    } else {
        SplitByNewlinePreservesCharsHelper(s, start, pos + 1, targetIndex);
    }
}

lemma ContainsTwoIntegersHasSpace(line: string)
    requires ContainsTwoIntegers(line)
    ensures ' ' in line
{
    var parts := SplitBySpace(line);
    assert |parts| == 2;
    SplitBySpaceHasSpace(line);
}

lemma SplitBySpaceHasSpace(s: string)
    requires |SplitBySpace(s)| >= 2
    ensures ' ' in s
{
    var parts := SplitBySpace(s);
    assert |parts| >= 2;
    SplitBySpaceHelperHasSpace(s, 0, 0);
}

lemma SplitBySpaceHelperHasSpace(s: string, start: nat, pos: nat)
    requires start <= |s| && pos <= |s|
    requires |SplitBySpaceHelper(s, start, pos)| >= 2
    ensures ' ' in s[pos..]
    decreases |s| - pos
{
    if pos >= |s| {
        assert false;
    } else if s[pos] == ' ' {
        
    } else {
        SplitBySpaceHelperHasSpace(s, start, pos + 1);
    }
}

lemma IntToStringDigitsOnly(n: nat)
    ensures forall c :: c in IntToString(n) ==> c in "0123456789"
{
    if n == 0 {
        assert IntToString(n) == "0";
    } else {
        IntToStringHelperDigitsOnly(n);
    }
}

lemma IntToStringHelperDigitsOnly(n: nat)
    requires n >= 0
    ensures forall c :: c in IntToStringHelper(n) ==> c in "0123456789"
{
    if n == 0 {
        
    } else {
        if n / 10 > 0 {
            IntToStringHelperDigitsOnly(n / 10);
        }
        var digit := (('0' as int) + (n % 10)) as char;
        assert digit in "0123456789";
    }
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires |s| > 0
    requires '\n' in s
    requires ValidInputFormat(s)
    ensures |result| > 0
    ensures forall c :: c in result ==> c in "0123456789\n"
    ensures IsValidCount(result)
    ensures result == CountWallSegments(s) + "\n"
    ensures result != s
// </vc-spec>
// <vc-code>
{
    var lines := SplitByNewline(s);
    var dims := ParseDimensions(lines[0]);
    var n := dims.0;
    var m := dims.1;

    var bottomRow := lines[n];

    var segments := CountConsecutiveBSegments(bottomRow);

    var segmentsStr := IntToString(segments);
    result := segmentsStr + "\n";

    assert forall c :: c in segmentsStr ==> c in "0123456789" by {
        IntToStringDigitsOnly(segments);
    }
    assert forall c :: c in result ==> c in "0123456789\n";
    assert IsValidCount(result);
    assert result == CountWallSegments(s) + "\n";

    assert forall c :: c in segmentsStr ==> c in "0123456789";
    assert result[|result|-1] == '\n';
    assert |result| >= 2;

    assert ' ' in lines[0] by {
        ContainsTwoIntegersHasSpace(lines[0]);
    }
    assert ' ' in s by {
        SplitByNewlinePreservesChars(s, lines[0], 0);
    }
    assert forall c :: c in result ==> c != ' ';
    assert result != s;
}
// </vc-code>

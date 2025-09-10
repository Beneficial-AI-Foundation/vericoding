predicate ContainsLowercase(s: string)
{
    exists i :: 0 <= i < |s| && 'a' <= s[i] <= 'z'
}

predicate ContainsUppercase(s: string)
{
    exists i :: 0 <= i < |s| && 'A' <= s[i] <= 'Z'
}

predicate ContainsDigit(s: string)
{
    exists i :: 0 <= i < |s| && '0' <= s[i] <= '9'
}

predicate IsValidPassword(s: string)
{
    |s| >= 5 && ContainsLowercase(s) && ContainsUppercase(s) && ContainsDigit(s)
}

function TrimNewline(s: string): string
{
    if |s| > 0 && s[|s|-1] == '\n' then s[..|s|-1] else s
}

function StripWhitespace(s: string): string
    decreases |s|
{
    if |s| == 0 then s
    else if s[0] == ' ' || s[0] == '\t' || s[0] == '\n' || s[0] == '\r' then
        StripWhitespace(s[1..])
    else if s[|s|-1] == ' ' || s[|s|-1] == '\t' || s[|s|-1] == '\n' || s[|s|-1] == '\r' then
        StripWhitespace(s[..|s|-1])
    else s
}

// <vc-helpers>
lemma StripWhitespacePreservesLengthProperty(s: string)
    ensures |StripWhitespace(s)| <= |s|
    decreases |s|
{
    if |s| == 0 {
        // Base case: empty string
    } else if s[0] == ' ' || s[0] == '\t' || s[0] == '\n' || s[0] == '\r' {
        StripWhitespacePreservesLengthProperty(s[1..]);
        assert |StripWhitespace(s)| == |StripWhitespace(s[1..])| <= |s[1..]| == |s| - 1 < |s|;
    } else if s[|s|-1] == ' ' || s[|s|-1] == '\t' || s[|s|-1] == '\n' || s[|s|-1] == '\r' {
        StripWhitespacePreservesLengthProperty(s[..|s|-1]);
        assert |StripWhitespace(s)| == |StripWhitespace(s[..|s|-1])| <= |s[..|s|-1]| == |s| - 1 < |s|;
    } else {
        // No whitespace to strip
        assert StripWhitespace(s) == s;
    }
}

lemma StripWhitespacePreservesCharacters(s: string, c: char, idx: int)
    requires 0 <= idx < |s|
    requires s[idx] == c
    requires c != ' ' && c != '\t' && c != '\n' && c != '\r'
    ensures exists i :: 0 <= i < |StripWhitespace(s)| && StripWhitespace(s)[i] == c
    decreases |s|
{
    if |s| == 0 {
        // Empty case, contradiction
    } else if s[0] == ' ' || s[0] == '\t' || s[0] == '\n' || s[0] == '\r' {
        if idx == 0 {
            // Contradiction: s[0] is whitespace but we assumed c is not
        } else {
            StripWhitespacePreservesCharacters(s[1..], c, idx - 1);
            var i :| 0 <= i < |StripWhitespace(s[1..])| && StripWhitespace(s[1..])[i] == c;
            assert StripWhitespace(s) == StripWhitespace(s[1..]);
        }
    } else if s[|s|-1] == ' ' || s[|s|-1] == '\t' || s[|s|-1] == '\n' || s[|s|-1] == '\r' {
        if idx == |s| - 1 {
            // Contradiction: s[|s|-1] is whitespace but we assumed c is not
        } else {
            StripWhitespacePreservesCharacters(s[..|s|-1], c, idx);
            var i :| 0 <= i < |StripWhitespace(s[..|s|-1])| && StripWhitespace(s[..|s|-1])[i] == c;
            assert StripWhitespace(s) == StripWhitespace(s[..|s|-1]);
        }
    } else {
        // No stripping needed, character is preserved
        assert StripWhitespace(s) == s;
        assert 0 <= idx < |s| && s[idx] == c;
    }
}

lemma StripWhitespacePreservesLowercase(s: string)
    ensures ContainsLowercase(s) ==> ContainsLowercase(StripWhitespace(s))
    decreases |s|
{
    if ContainsLowercase(s) {
        var i :| 0 <= i < |s| && 'a' <= s[i] <= 'z';
        StripWhitespacePreservesCharacters(s, s[i], i);
    }
}

lemma StripWhitespacePreservesUppercase(s: string)
    ensures ContainsUppercase(s) ==> ContainsUppercase(StripWhitespace(s))
    decreases |s|
{
    if ContainsUppercase(s) {
        var i :| 0 <= i < |s| && 'A' <= s[i] <= 'Z';
        StripWhitespacePreservesCharacters(s, s[i], i);
    }
}

lemma StripWhitespacePreservesDigit(s: string)
    ensures ContainsDigit(s) ==> ContainsDigit(StripWhitespace(s))
    decreases |s|
{
    if ContainsDigit(s) {
        var i :| 0 <= i < |s| && '0' <= s[i] <= '9';
        StripWhitespacePreservesCharacters(s, s[i], i);
    }
}

lemma StripWhitespacePreservesValidity(s: string)
    ensures IsValidPassword(s) ==> IsValidPassword(StripWhitespace(s))
    decreases |s|
{
    if IsValidPassword(s) {
        StripWhitespacePreservesLengthProperty(s);
        assert |StripWhitespace(s)| <= |s|;
        assert |s| >= 5 ==> |StripWhitespace(s)| >= 5;
        StripWhitespacePreservesLowercase(s);
        StripWhitespacePreservesUppercase(s);
        StripWhitespacePreservesDigit(s);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires |input| > 0
    ensures var processedInput := TrimNewline(input);
            var stripped := StripWhitespace(processedInput);
            if IsValidPassword(stripped) then
                output == "Correct\n"
            else
                output == "Too weak\n"
// </vc-spec>
// <vc-code>
{
    var processedInput := TrimNewline(input);
    var stripped := StripWhitespace(processedInput);
    
    if IsValidPassword(stripped) {
        output := "Correct\n";
    } else {
        output := "Too weak\n";
    }
}
// </vc-code>


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
lemma StripWhitespacePreservesLowercase(s: string)
    ensures ContainsLowercase(s) ==> ContainsLowercase(StripWhitespace(s))
    decreases |s|
{
    if ContainsLowercase(s) {
        var i :| 0 <= i < |s| && 'a' <= s[i] <= 'z';
        if |s| == 0 {
        } else if s[0] == ' ' || s[0] == '\t' || s[0] == '\n' || s[0] == '\r' {
            StripWhitespacePreservesLowercase(s[1..]);
        } else if s[|s|-1] == ' ' || s[|s|-1] == '\t' || s[|s|-1] == '\n' || s[|s|-1] == '\r' {
            StripWhitespacePreservesLowercase(s[..|s|-1]);
        } else {
        }
    }
}

lemma StripWhitespacePreservesUppercase(s: string)
    ensures ContainsUppercase(s) ==> ContainsUppercase(StripWhitespace(s))
    decreases |s|
{
    if ContainsUppercase(s) {
        var i :| 0 <= i < |s| && 'A' <= s[i] <= 'Z';
        if |s| == 0 {
        } else if s[0] == ' ' || s[0] == '\t' || s[0] == '\n' || s[0] == '\r' {
            StripWhitespacePreservesUppercase(s[1..]);
        } else if s[|s|-1] == ' ' || s[|s|-1] == '\t' || s[|s|-1] == '\n' || s[|s|-1] == '\r' {
            StripWhitespacePreservesUppercase(s[..|s|-1]);
        } else {
        }
    }
}

lemma StripWhitespacePreservesDigit(s: string)
    ensures ContainsDigit(s) ==> ContainsDigit(StripWhitespace(s))
    decreases |s|
{
    if ContainsDigit(s) {
        var i :| 0 <= i < |s| && '0' <= s[i] <= '9';
        if |s| == 0 {
        } else if s[0] == ' ' || s[0] == '\t' || s[0] == '\n' || s[0] == '\r' {
            StripWhitespacePreservesDigit(s[1..]);
        } else if s[|s|-1] == ' ' || s[|s|-1] == '\t' || s[|s|-1] == '\n' || s[|s|-1] == '\r' {
            StripWhitespacePreservesDigit(s[..|s|-1]);
        } else {
        }
    }
}

lemma StripWhitespaceMinLength(s: string)
    requires |s| >= 5
    ensures |StripWhitespace(s)| >= 5
    decreases |s|
{
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
    
    StripWhitespacePreservesLowercase(processedInput);
    StripWhitespacePreservesUppercase(processedInput);
    StripWhitespacePreservesDigit(processedInput);
    
    if IsValidPassword(stripped) {
        output := "Correct\n";
    } else {
        output := "Too weak\n";
    }
}
// </vc-code>


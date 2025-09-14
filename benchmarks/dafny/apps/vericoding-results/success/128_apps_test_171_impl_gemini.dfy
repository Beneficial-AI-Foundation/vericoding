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

    var hasLowercase := false;
    var hasUppercase := false;
    var hasDigit := false;

    var i := 0;
    while i < |stripped|
        invariant 0 <= i <= |stripped|
        invariant hasLowercase <==> (exists k :: 0 <= k < i && 'a' <= stripped[k] <= 'z')
        invariant hasUppercase <==> (exists k :: 0 <= k < i && 'A' <= stripped[k] <= 'Z')
        invariant hasDigit     <==> (exists k :: 0 <= k < i && '0' <= stripped[k] <= '9')
    {
        var c := stripped[i];
        if 'a' <= c <= 'z' {
            hasLowercase := true;
        }
        if 'A' <= c <= 'Z' {
            hasUppercase := true;
        }
        if '0' <= c <= '9' {
            hasDigit := true;
        }
        i := i + 1;
    }

    if |stripped| >= 5 && hasLowercase && hasUppercase && hasDigit {
        output := "Correct\n";
    } else {
        output := "Too weak\n";
    }
}
// </vc-code>


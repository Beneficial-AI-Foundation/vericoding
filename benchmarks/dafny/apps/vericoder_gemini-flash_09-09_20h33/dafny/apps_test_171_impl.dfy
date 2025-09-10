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
lemma lemma_StripWhitespace_preserves_content(s: string)
  ensures forall c | c in StripWhitespace(s) :: c in s
  ensures forall c | c in s && c != ' ' && c != '\t' && c != '\n' && c != '\r' :: c in StripWhitespace(s)
{
  if |s| == 0 {
    // Base case: empty string, nothing to prove.
  } else if s[0] == ' ' || s[0] == '\t' || s[0] == '\n' || s[0] == '\r' {
    lemma_StripWhitespace_preserves_content(s[1..]);
  } else if s[|s|-1] == ' ' || s[|s|-1] == '\t' || s[|s|-1] == '\n' || s[|s|-1] == '\r' {
    lemma_StripWhitespace_preserves_content(s[..|s|-1]);
  } else {
    // No change to content
  }
}

lemma lemma_TrimNewline_preserves_content(s: string)
  ensures forall c | c in TrimNewline(s) :: c in s
  ensures forall c | c in s && c != '\n' :: c in TrimNewline(s)
{
  if |s| > 0 && s[|s|-1] == '\n' {
    // If newline is trimmed, only the newline character is removed.
  } else {
    // No change to content.
  }
}

lemma lemma_chars_in_stripped(s: string)
  ensures forall c | c in StripWhitespace(TrimNewline(s)) :: c in s
  ensures forall c | c in s && c != ' ' && c != '\t' && c != '\n' && c != '\r' :: c in StripWhitespace(TrimNewline(s))
{
  lemma_TrimNewline_preserves_content(s);
  lemma_StripWhitespace_preserves_content(TrimNewline(s));
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

  lemma_chars_in_stripped(input); // Prove that char properties are preserved

  if IsValidPassword(stripped)
  {
    output := "Correct\n";
  }
  else
  {
    output := "Too weak\n";
  }
}
// </vc-code>


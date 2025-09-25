// <vc-preamble>
// Check if a character is an uppercase alphabet letter
predicate IsUpperAlpha(c: char)
{
    'A' <= c <= 'Z'
}

// Check if a character is a lowercase alphabet letter  
predicate IsLowerAlpha(c: char)
{
    'a' <= c <= 'z'
}

// Determine if a character is alphabetic
predicate IsAlpha(c: char)
{
    IsUpperAlpha(c) || IsLowerAlpha(c)
}

// Convert a single character to lowercase (simplified for Dafny)
function ToLower(c: char): char
{
    if IsUpperAlpha(c) then
        // Simplified: assume conversion works for spec purposes
        c // This would be the lowercase version in practice
    else
        c
}

// Normalize a character: keep only lowercase letters
function NormalizeChar(c: char): seq<char>
{
    if IsAlpha(c) then
        [ToLower(c)]
    else
        []
}

// Normalize a string into a sequence of lowercase alphabetic characters
function NormalizeString(s: string): seq<char>
{
    if |s| == 0 then
        []
    else
        NormalizeChar(s[0]) + NormalizeString(s[1..])
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method IsCleanPalindrome(s: string) returns (result: bool)
    ensures result == (NormalizeString(s) == NormalizeString(s)[..|NormalizeString(s)|])
// </vc-spec>
// <vc-code>
{
    // TODO: implement
    assume {:axiom} false;
}
// </vc-code>

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
function ReverseSeq<T>(a: seq<T>): seq<T>
  decreases |a|
{
  if |a| == 0 then
    []
  else
    ReverseSeq(a[1..]) + [a[0]]
}

/* helper modified by LLM (iteration 2): adjusted IsPalindromeSeq to require equality on type parameter T */
function IsPalindromeSeq<T(==)>(a: seq<T>): bool
  decreases |a|
{
  if |a| <= 1 then
    true
  else
    a[0] == a[|a|-1] && IsPalindromeSeq(a[1..|a|-1])
}

// </vc-helpers>

// <vc-spec>
method IsCleanPalindrome(s: string) returns (result: bool)
    ensures result == (NormalizeString(s) == NormalizeString(s)[..|NormalizeString(s)|])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implemented by normalizing once and comparing full slice */
  var ns := NormalizeString(s);
  result := ns == ns[..|ns|];
}

// </vc-code>

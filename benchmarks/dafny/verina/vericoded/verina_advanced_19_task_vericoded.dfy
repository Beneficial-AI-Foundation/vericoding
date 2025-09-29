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
/* helper modified by LLM (iteration 5): Fixed sequence concatenation in ReverseAppend lemma */
function ReverseSeq(s: seq<char>): seq<char>
{
    if |s| == 0 then []
    else ReverseSeq(s[1..]) + [s[0]]
}

function IsPalindromeSeq(s: seq<char>): bool
{
    s == ReverseSeq(s)
}

lemma ReverseAppend(s: seq<char>, c: char)
    ensures ReverseSeq(s + [c]) == [c] + ReverseSeq(s)
{
    if |s| == 0 {
        assert s + [c] == [c];
        assert ReverseSeq([c]) == [c];
        assert ReverseSeq(s) == [];
    } else {
        assert s + [c] == [s[0]] + (s[1..] + [c]);
        calc {
            ReverseSeq(s + [c]);
            == ReverseSeq([s[0]] + (s[1..] + [c]));
            == ReverseSeq((s[1..] + [c])) + [s[0]];
            == { ReverseAppend(s[1..], c); }
               ([c] + ReverseSeq(s[1..])) + [s[0]];
            == [c] + (ReverseSeq(s[1..]) + [s[0]]);
            == [c] + ReverseSeq(s);
        }
    }
}

lemma ReverseInvolution(s: seq<char>)
    ensures ReverseSeq(ReverseSeq(s)) == s
{
    if |s| == 0 {
    } else {
        calc {
            ReverseSeq(ReverseSeq(s));
            == ReverseSeq(ReverseSeq(s[1..]) + [s[0]]);
            == { ReverseAppend(ReverseSeq(s[1..]), s[0]); }
               [s[0]] + ReverseSeq(ReverseSeq(s[1..]));
            == { ReverseInvolution(s[1..]); }
               [s[0]] + s[1..];
            == s;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method IsCleanPalindrome(s: string) returns (result: bool)
    ensures result == (NormalizeString(s) == NormalizeString(s)[..|NormalizeString(s)|])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Simply check palindrome property without assertions */
{
    var normalized := NormalizeString(s);
    result := normalized == normalized[..|normalized|];
}
// </vc-code>

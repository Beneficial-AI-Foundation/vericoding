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
/* helper modified by LLM (iteration 3): Fixed palindrome equivalence proof with proper index mapping */
function Reverse(s: seq<char>): seq<char>
{
    if |s| == 0 then []
    else Reverse(s[1..]) + [s[0]]
}

lemma ReverseLengthLemma(s: seq<char>)
    ensures |Reverse(s)| == |s|
{
    if |s| == 0 {
    } else {
        ReverseLengthLemma(s[1..]);
    }
}

lemma ReverseIndexLemma(s: seq<char>, i: int)
    requires 0 <= i < |s|
    ensures |Reverse(s)| == |s|
    ensures Reverse(s)[i] == s[|s| - 1 - i]
{
    ReverseLengthLemma(s);
    if |s| == 1 {
        assert Reverse(s) == [s[0]];
    } else {
        var tail := s[1..];
        if i == |s| - 1 {
            assert Reverse(s) == Reverse(tail) + [s[0]];
            assert Reverse(s)[i] == s[0];
        } else {
            ReverseIndexLemma(tail, i);
            assert Reverse(s) == Reverse(tail) + [s[0]];
            assert Reverse(s)[i] == Reverse(tail)[i];
            assert Reverse(tail)[i] == tail[|tail| - 1 - i];
            assert tail[|tail| - 1 - i] == s[|s| - 1 - i];
        }
    }
}

lemma ReverseProperty(s: seq<char>)
    ensures s == Reverse(s) <==> (forall i :: 0 <= i < |s| ==> s[i] == s[|s| - 1 - i])
{
    ReverseLengthLemma(s);
    
    if s == Reverse(s) {
        forall i | 0 <= i < |s|
            ensures s[i] == s[|s| - 1 - i]
        {
            ReverseIndexLemma(s, i);
            assert s[i] == Reverse(s)[i] == s[|s| - 1 - i];
        }
    }
    
    if (forall i :: 0 <= i < |s| ==> s[i] == s[|s| - 1 - i]) {
        forall i | 0 <= i < |s|
            ensures s[i] == Reverse(s)[i]
        {
            ReverseIndexLemma(s, i);
            assert s[i] == s[|s| - 1 - i] == Reverse(s)[i];
        }
        assert s == Reverse(s);
    }
}
// </vc-helpers>

// <vc-spec>
method IsCleanPalindrome(s: string) returns (result: bool)
    ensures result == (NormalizeString(s) == NormalizeString(s)[..|NormalizeString(s)|])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed postcondition to match spec requirements using proper sequence slicing */
    var normalized := NormalizeString(s);
    var reversed := Reverse(normalized);
    ReverseProperty(normalized);
    result := normalized == normalized[..|normalized|];
}
// </vc-code>

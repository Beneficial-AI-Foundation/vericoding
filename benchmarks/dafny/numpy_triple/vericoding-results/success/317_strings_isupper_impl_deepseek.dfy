// <vc-preamble>
// Helper predicate to determine if a character is alphabetic
predicate IsAlpha(c: char)
{
    ('a' <= c <= 'z') || ('A' <= c <= 'Z')
}

// Helper predicate to determine if a character is uppercase
predicate IsUpper(c: char)
{
    'A' <= c <= 'Z'
}

// Helper predicate to check if a string has at least one alphabetic character
predicate HasAlphaChar(s: string)
{
    exists i :: 0 <= i < |s| && IsAlpha(s[i])
}

// Helper predicate to check if all alphabetic characters in a string are uppercase
predicate AllAlphaAreUpper(s: string)
{
    forall i :: 0 <= i < |s| && IsAlpha(s[i]) ==> IsUpper(s[i])
}

// Main method implementing numpy.strings.isupper behavior
// </vc-preamble>

// <vc-helpers>
function HasAlphaCharFn(s: string): bool
{
    exists i :: 0 <= i < |s| && IsAlpha(s[i])
}

function AllAlphaAreUpperFn(s: string): bool
{
    forall i :: 0 <= i < |s| ==> (IsAlpha(s[i]) ==> IsUpper(s[i]))
}

/* helper modified by LLM (iteration 3): Added lemma to connect helper predicates with functions */
lemma Lemma_HasAlphaChar_Equivalent(s: string)
    ensures HasAlphaChar(s) == HasAlphaCharFn(s)
{
}

lemma Lemma_AllAlphaAreUpper_Equivalent(s: string)
    ensures AllAlphaAreUpper(s) == AllAlphaAreUpperFn(s)
{
}
// </vc-helpers>

// <vc-spec>
method IsUpperStrings(a: seq<string>) returns (result: seq<bool>)
    // Output sequence has same length as input
    ensures |result| == |a|
    // Each result element is true iff the corresponding string has:
    // 1. At least one character (length > 0)
    // 2. At least one alphabetic character 
    // 3. All alphabetic characters are uppercase
    ensures forall i :: 0 <= i < |a| ==> 
        result[i] == (|a[i]| > 0 && HasAlphaChar(a[i]) && AllAlphaAreUpper(a[i]))
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 3): Added lemma calls and fixed index access with loop invariant */
    result := [];
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> 
            result[j] == (|a[j]| > 0 && HasAlphaCharFn(a[j]) && AllAlphaAreUpperFn(a[j]))
    {
        Lemma_HasAlphaChar_Equivalent(a[i]);
        Lemma_AllAlphaAreUpper_Equivalent(a[i]);
        var current_result := |a[i]| > 0 && HasAlphaCharFn(a[i]) && AllAlphaAreUpperFn(a[i]);
        result := result + [current_result];
        i := i + 1;
    }
}
// </vc-code>

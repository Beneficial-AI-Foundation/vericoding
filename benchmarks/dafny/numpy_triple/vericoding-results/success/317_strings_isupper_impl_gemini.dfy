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
/* helper modified by LLM (iteration 2): Re-submitted helper as it is logically sound and did not cause errors. */
method ComputeIsUpperForString(s: string) returns (is_upper_string: bool)
    ensures is_upper_string == (|s| > 0 && HasAlphaChar(s) && AllAlphaAreUpper(s))
{
    var has_alpha := false;
    var all_are_upper := true;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant has_alpha == (exists k :: 0 <= k < i && IsAlpha(s[k]))
        invariant all_are_upper == (forall k :: 0 <= k < i && IsAlpha(s[k]) ==> IsUpper(s[k]))
    {
        if IsAlpha(s[i]) {
            has_alpha := true;
            if !IsUpper(s[i]) {
                all_are_upper := false;
            }
        }
        i := i + 1;
    }
    is_upper_string := |s| > 0 && has_alpha && all_are_upper;
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
    /* code modified by LLM (iteration 2): Fixed compilation errors by using sequence operations instead of array operations. */
    result := [];
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] == (|a[j]| > 0 && HasAlphaChar(a[j]) && AllAlphaAreUpper(a[j]))
    {
        var is_upper := ComputeIsUpperForString(a[i]);
        result := result + [is_upper];
        i := i + 1;
    }
}
// </vc-code>

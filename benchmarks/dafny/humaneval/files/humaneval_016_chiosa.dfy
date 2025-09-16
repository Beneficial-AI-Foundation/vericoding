// <vc-preamble>
// ======= TASK =======
// Count the number of distinct characters in a string, ignoring case differences.
// Input: A string
// Output: Integer representing the count of unique characters
// Case-insensitive comparison (treat 'A' and 'a' as the same character)

// ======= SPEC REQUIREMENTS =======
function to_lower_char(c: char): char
{
    if 'A' <= c <= 'Z' then
        (c as int - 'A' as int + 'a' as int) as char
    else
        c
}
// </vc-preamble>

// <vc-helpers>
// ======= HELPERS =======
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method count_distinct_characters(s: string) returns (count: int)
    ensures count >= 0
    ensures count <= |s|
    ensures count == |set i | 0 <= i < |s| :: to_lower_char(s[i])|
// </vc-spec>
// <vc-code>
{
    var i := 0;
    var chars := {};
    while i < |s|
        invariant 0 <= i <= |s|
        invariant chars == set j | 0 <= j < i :: to_lower_char(s[j])
        invariant |chars| <= i
    {
        chars := chars + {to_lower_char(s[i])};
        i := i + 1;
    }
    count := |chars|;
}
// </vc-code>

// <vc-preamble>
// ======= TASK =======
// Given a string s, determine if it is "happy". A string is happy if and only if:
// 1. Its length is at least 3, AND
// 2. In every substring of 3 consecutive characters, all characters are distinct (no duplicates)

// ======= SPEC REQUIREMENTS =======
predicate ValidLength(s: string)
{
    |s| >= 3
}

predicate AllWindowsDistinct(s: string)
{
    forall i :: 0 <= i <= |s| - 3 ==> s[i] != s[i+1] && s[i] != s[i+2] && s[i+1] != s[i+2]
}

predicate IsHappy(s: string)
{
    ValidLength(s) && AllWindowsDistinct(s)
}
// </vc-preamble>

// <vc-helpers>
// ======= HELPERS =======
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method is_happy(s: string) returns (result: bool)
    ensures result == IsHappy(s)
// </vc-spec>
// <vc-code>
{
    if |s| < 3 {
        return false;
    }

    var i := 0;
    while i <= |s| - 3 
        invariant 0 <= i <= |s| - 2
        invariant forall j :: 0 <= j < i ==> s[j] != s[j+1] && s[j] != s[j+2] && s[j+1] != s[j+2]
    {
        if s[i] == s[i+1] || s[i] == s[i+2] || s[i+1] == s[i+2] {
            return false;
        }
        i := i + 1;
    }

    return true;
}
// </vc-code>

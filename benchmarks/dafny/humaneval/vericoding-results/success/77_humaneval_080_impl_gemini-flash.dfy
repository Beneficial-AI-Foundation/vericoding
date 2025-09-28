// <vc-preamble>

predicate ValidLength(s: string)
{
    |s| >= 3
}

predicate AllWindowsDistinct(s: string)
{
    forall i {:trigger s[i]} :: 0 <= i <= |s| - 3 ==> s[i] != s[i+1] && s[i] != s[i+2] && s[i+1] != s[i+2]
}

predicate IsHappy(s: string)
{
    ValidLength(s) && AllWindowsDistinct(s)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Removed redundant predicate definition `AllWindowsDistinct` to resolve duplicate member name error. */
// </vc-helpers>

// <vc-spec>
method is_happy(s: string) returns (result: bool)
    ensures result == IsHappy(s)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): directly call the `IsHappy` predicate defined in the preamble to ensure postcondition is met */
{
    result := IsHappy(s);
}
// </vc-code>

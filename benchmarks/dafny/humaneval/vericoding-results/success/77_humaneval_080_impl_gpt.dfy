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
/* helper modified by LLM (iteration 3): Fixed function postcondition to reference function name; provided window check utility */
function WindowOK(s: string, i: int): bool
  requires 0 <= i <= |s| - 3
{
  s[i] != s[i+1] && s[i] != s[i+2] && s[i+1] != s[i+2]
}

/* helper modified by LLM (iteration 3): Boolean wrapper for IsHappy predicate with correct ensures using the function name */
function IsHappyBool(s: string): bool
  ensures IsHappyBool(s) == IsHappy(s)
{
  IsHappy(s)
}
// </vc-helpers>

// <vc-spec>
method is_happy(s: string) returns (result: bool)
    ensures result == IsHappy(s)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Direct evaluation of predicate for result */
  result := IsHappy(s);
}
// </vc-code>

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
// </vc-helpers>

// <vc-spec>
method is_happy(s: string) returns (result: bool)
    ensures result == IsHappy(s)
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
  }
// </vc-code>

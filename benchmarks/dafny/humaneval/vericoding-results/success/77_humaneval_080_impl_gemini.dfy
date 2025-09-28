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
  /* code modified by LLM (iteration 2): Added trigger to loop invariant to fix compilation warning. */
  if |s| < 3 {
    result := false;
    return;
  }

  result := true;
  var i := 0;
  while i <= |s| - 3
    invariant 0 <= i <= |s| - 2
    invariant forall k {:trigger s[k]} :: 0 <= k < i ==> s[k] != s[k+1] && s[k] != s[k+2] && s[k+1] != s[k+2]
  {
    if s[i] == s[i+1] || s[i] == s[i+2] || s[i+1] == s[i+2] {
      result := false;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>

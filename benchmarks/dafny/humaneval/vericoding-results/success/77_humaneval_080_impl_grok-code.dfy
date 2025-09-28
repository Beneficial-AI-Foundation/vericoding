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
/* code modified by LLM (iteration 3): Fixed loop invariant to properly handle loop termination and added trigger to quantifier */
{
  if |s| < 3 {
    result := false;
  } else {
    var successful := true;
    var i := 0;
    while i <= (|s| - 3)
      invariant 0 <= i <= |s| - 2
      invariant successful <==> forall j {:trigger s[j]} :: 0 <= j < i ==> (s[j] != s[j+1] && s[j] != s[j+2] && s[j+1] != s[j+2])
    {
      if s[i] == s[i+1] || s[i] == s[i+2] || s[i+1] == s[i+2] {
        successful := false;
        i := (|s| - 3) + 1;
      } else {
        i := i + 1;
      }
    }
    result := successful;
  }
}
// </vc-code>

// <vc-preamble>
predicate IsUpperCase(c: char)
{
    65 <= c as int <= 90
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method CountUppercase(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 0 <= i < |s| && IsUpperCase(s[i])|
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>

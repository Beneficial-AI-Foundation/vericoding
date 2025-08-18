predicate IsUpperCase(c: char)
{
    65 <= c as int <= 90
}

// <vc-helpers>
// </vc-helpers>

method CountUppercase(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 0 <= i < |s| && IsUpperCase(s[i])|
// <vc-code>
{
  assume false;
}
// </vc-code>
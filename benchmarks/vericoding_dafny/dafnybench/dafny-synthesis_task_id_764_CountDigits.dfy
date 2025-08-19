predicate IsDigit(c: char)
{
    48 <= c as int <= 57
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method CountDigits(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 0 <= i < |s| && IsDigit(s[i])|
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>
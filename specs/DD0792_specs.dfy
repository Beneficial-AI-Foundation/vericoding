// <vc-preamble>
predicate IsDigit(c: char)
{
    48 <= c as int <= 57
}
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method CountDigits(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 0 <= i < |s| && IsDigit(s[i])|
// </vc-spec>
// <vc-code>
{
    var digits := set i: int | 0 <= i < |s| && IsDigit(s[i]);
    count := |digits|;
}
// </vc-code>

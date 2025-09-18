// <vc-preamble>
predicate IsDigit(c: char)
{
    '0' <= c <= '9'
}
// </vc-preamble>

// <vc-helpers>
function CountDigitsFrom(s: string, i: nat): nat
    requires i <= |s|
    decreases |s| - i
{
    if i == |s| then 0 else (if IsDigit(s[i]) then 1 else 0) + CountDigitsFrom(s, i+1)
}
// </vc-helpers>

// <vc-spec>
method CountDigits(s: string) returns (result: nat)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  result := CountDigitsFrom(s, 0);
}
// </vc-code>

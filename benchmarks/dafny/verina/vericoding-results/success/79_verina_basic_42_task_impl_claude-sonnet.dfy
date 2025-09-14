// <vc-preamble>
predicate IsDigit(c: char)
{
    '0' <= c <= '9'
}
// </vc-preamble>

// <vc-helpers>
function CountDigitsInString(s: string): nat
{
    if |s| == 0 then 0
    else (if IsDigit(s[0]) then 1 else 0) + CountDigitsInString(s[1..])
}
// </vc-helpers>

// <vc-spec>
method CountDigits(s: string) returns (result: nat)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    result := CountDigitsInString(s);
}
// </vc-code>

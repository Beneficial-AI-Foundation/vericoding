// <vc-preamble>
predicate IsDigit(c: char)
{
    '0' <= c <= '9'
}
// </vc-preamble>

// <vc-helpers>
function CountDigits_Helper(s: string): (count: nat)
    decreases s
{
    if s == "" then 0
    else (if IsDigit(s[0]) then 1 else 0) + CountDigits_Helper(s[1..])
}
// </vc-helpers>

// <vc-spec>
method CountDigits(s: string) returns (result: nat)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    result := CountDigits_Helper(s);
}
// </vc-code>

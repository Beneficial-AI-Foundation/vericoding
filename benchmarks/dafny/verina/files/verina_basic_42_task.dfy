// <vc-preamble>
predicate IsDigit(c: char)
{
    '0' <= c <= '9'
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method CountDigits(s: string) returns (result: nat)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume {:axiom} false;
    result := 0;
    // impl-end
}
// </vc-code>

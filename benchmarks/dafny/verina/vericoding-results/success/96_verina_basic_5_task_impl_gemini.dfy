// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function mult_pos(a: int, b: nat): int
{
    if b == 0 then 0
    else a + mult_pos(a, b - 1)
}

lemma MulPosIsMul(a: int, b: nat)
    ensures mult_pos(a, b) == a * b
{
    if b > 0 {
        MulPosIsMul(a, b - 1);
    }
}
// </vc-helpers>

// <vc-spec>
method multiply(a: int, b: int) returns (result: int)
    ensures result == a * b
// </vc-spec>
// <vc-code>
{
    if b >= 0 {
        MulPosIsMul(a, b as nat);
        result := mult_pos(a, b as nat);
    } else {
        MulPosIsMul(a, (-b) as nat);
        result := -mult_pos(a, (-b) as nat);
    }
}
// </vc-code>

// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
function last_digit(n: nat): nat
// </vc-spec>
// <vc-code>
{
    n % 10
}

lemma last_digit_correct(n: nat)
    ensures
        last_digit(n) < 10
    ensures
        last_digit(n) == n % 10
{
    
}
// </vc-code>

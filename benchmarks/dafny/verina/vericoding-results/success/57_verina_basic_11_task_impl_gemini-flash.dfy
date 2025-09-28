// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
function last_digit(n: nat): nat
// </vc-spec>
// <vc-code>
{
    // impl-start
    // TODO: implement
    n % 10
    // impl-end
}

lemma last_digit_correct(n: nat)
    ensures
        last_digit(n) < 10
    ensures
        last_digit(n) == n % 10
{
    // impl-start
    // TODO: Implement proof
    // The correctness of n % 10 is inherent to the definition of the modulo operator.
    // Since n is a natural number, n % 10 will always be in the range [0, 9].
    // last_digit(n) is defined as n % 10, so the postconditions follow directly from the definition.
    // No explicit steps are needed for this simple proof as Dafny's SMT solver can deduce these properties.
    // impl-end
}
// </vc-code>

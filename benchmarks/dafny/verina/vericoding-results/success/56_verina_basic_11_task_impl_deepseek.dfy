// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma last_digit_less(n: nat)
    ensures last_digit(n) < 10
{
    // By the definition of modulus
    if n < 10 {
        // When n < 10, last_digit(n) = n, which is < 10
        assert last_digit(n) == n;
        assert n < 10;
    } else {
        // When n >= 10, last_digit(n) = n % 10, which is always < 10
        assert last_digit(n) == n % 10;
        assert n % 10 < 10;
    }
}

lemma modulus_property(n: nat)
    ensures n % 10 == n - (n / 10) * 10
{
    // This follows from the standard property of modulus
    // No need for complex proof, Dafny's math axioms handle this
}
// </vc-helpers>

// <vc-spec>
function last_digit(n: nat): nat
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fix syntax and ensure proper returns */
    if n < 10 then n else n % 10
}

lemma last_digit_correct(n: nat)
    ensures
        last_digit(n) < 10
    ensures
        last_digit(n) == n % 10
{
    // Call helper lemmas to prove the properties
    last_digit_less(n);
    
    // Show that the implementation satisfies n % 10
    if n < 10 {
        // When n < 10, n % 10 = n (by modulus definition)
        assert n % 10 == n;
    } else {
        // When n >= 10, the implementation returns n % 10 directly
        assert n % 10 == n % 10;
    }
}
// </vc-code>

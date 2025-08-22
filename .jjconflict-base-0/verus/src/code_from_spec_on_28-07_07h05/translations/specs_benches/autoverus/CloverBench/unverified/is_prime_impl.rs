/* code modified by LLM (iteration 2): converted from Rust/Verus to proper Dafny syntax */

predicate divides(factor: nat, candidate: nat) {
    candidate % factor == 0
}

predicate is_prime(candidate: nat) {
    && 1 < candidate
    && forall factor: nat :: 1 < factor && factor < candidate ==> !divides(factor, candidate)
}

/* code modified by LLM (iteration 2): added lemma to establish equivalence between full check and sqrt check */
lemma lemma_prime_check_equivalence(candidate: nat)
    requires 1 < candidate
    ensures
        (forall factor: nat :: 1 < factor && factor < candidate ==> !divides(factor, candidate)) 
        <==> 
        (forall factor: nat :: 1 < factor && factor * factor <= candidate ==> !divides(factor, candidate))
{
    if forall factor: nat :: 1 < factor && factor * factor <= candidate ==> !divides(factor, candidate) {
        forall factor: nat | 1 < factor && factor < candidate
            ensures !divides(factor, candidate)
        {
            if divides(factor, candidate) {
                if factor * factor <= candidate {
                    assert false;  // contradiction with our assumption
                } else {
                    var cofactor := candidate / factor;
                    assert candidate == factor * cofactor;
                    assert 1 < cofactor < factor;
                    assert cofactor * cofactor < factor * cofactor == candidate;
                    assert !divides(cofactor, candidate);  // contradiction
                    assert false;
                }
            }
        }
    }
}

method test_prime(candidate: nat) returns (result: bool)
    requires 1 < candidate
    ensures result == is_prime(candidate)
{
    /* code modified by LLM (iteration 2): handle small cases first */
    if candidate <= 3 {
        return true;  // 2 and 3 are prime
    }
    
    /* code modified by LLM (iteration 2): use proper Dafny loop with factor checking up to sqrt */
    var factor := 2;
    while factor * factor <= candidate
        invariant 2 <= factor
        invariant forall f: nat :: 2 <= f < factor ==> !divides(f, candidate)
        decreases candidate - factor * factor
    {
        if candidate % factor == 0 {
            /* code modified by LLM (iteration 2): found a divisor, so not prime */
            assert divides(factor, candidate);
            assert 1 < factor < candidate;
            return false;
        }
        factor := factor + 1;
    }
    
    /* code modified by LLM (iteration 2): prove that we've checked all necessary factors */
    lemma_prime_check_equivalence(candidate);
    assert forall f: nat :: 2 <= f && f * f <= candidate ==> !divides(f, candidate);
    
    return true;
}
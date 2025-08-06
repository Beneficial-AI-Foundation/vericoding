use vstd::prelude::*;

fn main() {}
verus! {

spec fn divides(factor: nat, candidate: nat) -> bool {
    candidate % factor == 0
}

spec fn is_prime(candidate: nat) -> bool {
    &&& 1 < candidate
    &&& forall|factor: nat| 1 < factor && factor < candidate ==> !divides(factor, candidate)
}

fn test_prime(candidate: u64) -> (result: bool)
    requires
        1 < candidate,
    ensures
        result == is_prime(candidate as nat),
{
    let mut i: u64 = 2;
    
    while i * i <= candidate
        invariant
            2 <= i <= candidate,
            forall|factor: nat| 2 <= factor < i ==> !divides(factor, candidate as nat),
    {
        if candidate % i == 0 {
            /* code modified by LLM (iteration 2): Fixed assertion syntax by properly parenthesizing cast expressions */
            assert(divides(i as nat, candidate as nat));
            assert(2 <= (i as nat));
            assert((i as nat) < (candidate as nat));
            return false;
        }
        i = i + 1;
    }
    
    /* code modified by LLM (iteration 2): Added proof block for the final assertion */
    proof {
        assert forall|factor: nat| 2 <= factor < candidate as nat implies !divides(factor, candidate as nat) by {
            if divides(factor, candidate as nat) {
                let quotient = (candidate as nat) / factor;
                assert(candidate as nat == factor * quotient);
                assert(quotient >= 1);
                
                if factor < i as nat {
                    // We already checked this range in our loop
                    assert(!divides(factor, candidate as nat));
                    assert(false);
                } else {
                    // factor >= i, and i * i > candidate
                    assert(factor >= i as nat);
                    assert((i as nat) * (i as nat) > candidate as nat);
                    
                    // Since factor * quotient = candidate and factor >= i > sqrt(candidate)
                    // we have quotient = candidate / factor <= candidate / i < i
                    assert(quotient * factor == candidate as nat);
                    assert(quotient < i as nat);
                    
                    if quotient >= 2 {
                        assert(2 <= quotient && quotient < i as nat);
                        assert(!divides(quotient, candidate as nat));
                        assert(false);
                    } else {
                        // quotient == 1, so factor == candidate, but factor < candidate
                        assert(quotient == 1);
                        assert(candidate as nat == factor);
                        assert(factor < candidate as nat);
                        assert(false);
                    }
                }
            }
        };
    }
    
    true
}

} // verus!
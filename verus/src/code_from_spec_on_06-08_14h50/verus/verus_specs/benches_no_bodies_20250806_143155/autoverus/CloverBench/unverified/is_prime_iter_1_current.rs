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
            // Found a divisor, so not prime
            assert(divides(i as nat, candidate as nat));
            assert(2 <= i as nat < candidate as nat);
            return false;
        }
        i = i + 1;
    }
    
    // No divisor found up to sqrt(candidate)
    // Need to prove this implies no divisor exists from 2 to candidate-1
    assert forall|factor: nat| 2 <= factor < candidate as nat implies !divides(factor, candidate as nat) by {
        if divides(factor, candidate as nat) {
            // If factor divides candidate, then candidate = factor * quotient for some quotient
            let quotient = (candidate as nat) / factor;
            assert(candidate as nat == factor * quotient);
            assert(quotient >= 1);
            
            if factor <= i as nat - 1 {
                // We already checked this range in our loop
                assert(!divides(factor, candidate as nat));
                assert(false);
            } else {
                // factor > i - 1, so factor >= i
                // Since i * i > candidate, we have factor >= i > sqrt(candidate)
                // But then quotient = candidate / factor < candidate / sqrt(candidate) = sqrt(candidate)
                // So quotient < sqrt(candidate) <= i - 1 < factor
                // This means quotient < factor, and since quotient * factor = candidate,
                // quotient must be a divisor we already checked
                assert(factor >= i as nat);
                assert((i as nat) * (i as nat) > candidate as nat);
                assert(quotient < i as nat);
                assert(quotient >= 1);
                if quotient >= 2 {
                    assert(2 <= quotient < i as nat);
                    assert(!divides(quotient, candidate as nat));
                    assert(false);
                } else {
                    assert(quotient == 1);
                    assert(candidate as nat == factor);
                    assert(factor < candidate as nat);
                    assert(false);
                }
            }
        }
    };
    
    true
}

} // verus!
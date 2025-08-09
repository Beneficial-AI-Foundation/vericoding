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
            return false;
        }
        i = i + 1;
    }
    
    proof {
        // Prove that checking up to sqrt is sufficient
        assert forall|factor: nat| 1 < factor && factor < candidate ==> !divides(factor, candidate as nat) by {
            if 1 < factor && factor < candidate {
                if factor < i {
                    // Already checked in loop
                    assert(!divides(factor, candidate as nat));
                } else {
                    // factor >= i, so factor >= sqrt(candidate)
                    // If factor divides candidate, then candidate/factor <= sqrt(candidate)
                    // But we already checked all divisors up to sqrt(candidate)
                    assert(factor >= i);
                    assert(i * i > candidate);
                    if divides(factor, candidate as nat) {
                        let quotient = candidate as nat / factor;
                        assert(quotient * factor == candidate as nat);
                        assert(quotient < factor); // since factor > sqrt(candidate)
                        assert(1 < quotient); // since factor < candidate
                        assert(divides(quotient, candidate as nat));
                        assert(2 <= quotient < i); // contradiction with loop invariant
                        assert(false);
                    }
                }
            }
        }
    }
    
    true
}

} // verus!
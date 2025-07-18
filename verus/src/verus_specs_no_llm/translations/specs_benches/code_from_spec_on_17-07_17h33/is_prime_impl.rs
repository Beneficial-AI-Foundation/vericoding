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
    let mut factor = 2;
    while factor < candidate
        invariant
            2 <= factor <= candidate,
            forall|f: nat| 2 <= f < factor ==> !divides(f, candidate as nat),
        /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
        decreases candidate - factor
    {
        if candidate % factor == 0 {
            /* code modified by LLM (iteration 1): added assertion to prove that finding a divisor means not prime */
            assert(divides(factor as nat, candidate as nat));
            assert(1 < factor && factor < candidate);
            assert(!is_prime(candidate as nat));
            return false;
        }
        factor = factor + 1;
    }
    /* code modified by LLM (iteration 1): added assertion to prove that no divisors found means prime */
    assert(forall|f: nat| 2 <= f < candidate ==> !divides(f, candidate as nat));
    assert(forall|f: nat| 1 < f && f < candidate ==> !divides(f, candidate as nat));
    assert(is_prime(candidate as nat));
    return true;
}

} // verus!
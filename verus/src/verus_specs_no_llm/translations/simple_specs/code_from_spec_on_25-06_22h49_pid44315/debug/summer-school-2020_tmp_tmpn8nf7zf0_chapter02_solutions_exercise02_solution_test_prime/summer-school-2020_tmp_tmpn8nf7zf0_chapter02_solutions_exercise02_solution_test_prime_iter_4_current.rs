use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn divides(f: nat, i: nat) -> bool
    requires 1 <= f
{
    i % f == 0
}

spec fn IsPrime(i: nat) -> bool {
    && 1 < i
    && (forall f: nat :: 1 < f < i ==> !divides(f, i))
}

fn test_prime(i: nat) -> (result: bool)
    requires
        1 < i
    ensures
        result == IsPrime(i)
{
    let mut f: nat = 2;
    
    while f < i
        invariant
            1 < i,
            2 <= f <= i,
            forall g: nat :: 1 < g < f ==> !divides(g, i)
        decreases i - f
    {
        // Assert preconditions for the modulo operation
        assert(f >= 1);
        assert(f > 0);
        
        if i % f == 0 {
            // We found a divisor, so i is not prime
            assert(divides(f, i));
            assert(1 < f < i);
            // This proves that IsPrime(i) is false
            assert(!IsPrime(i));
            return false;
        }
        
        // f does not divide i
        assert(!divides(f, i));
        f = f + 1;
    }
    
    // Loop has finished, so f == i
    assert(f == i);
    // We've checked all numbers from 2 to i-1 and none divide i
    assert(forall g: nat :: 1 < g < i ==> !divides(g, i));
    // This means i is prime
    assert(IsPrime(i));
    true
}

}
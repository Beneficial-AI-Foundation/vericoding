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
        assert(f >= 1); // This is needed for the divides precondition
        
        if i % f == 0 {
            assert(divides(f, i));
            assert(1 < f < i);
            return false;
        }
        
        assert(!divides(f, i));
        f = f + 1;
    }
    
    assert(f == i);
    assert(forall g: nat :: 1 < g < i ==> !divides(g, i));
    true
}

}
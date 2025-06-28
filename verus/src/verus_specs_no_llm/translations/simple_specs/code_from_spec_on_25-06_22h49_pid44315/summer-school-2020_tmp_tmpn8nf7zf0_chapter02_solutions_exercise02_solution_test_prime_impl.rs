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

fn test_prime(i: u32) -> (result: bool)
    requires
        1 < i
    ensures
        result == IsPrime(i as nat)
{
    let mut f: u32 = 2;
    
    while f < i
        invariant
            1 < i,
            2 <= f <= i,
            forall g: nat :: 2 <= g < f ==> !divides(g, i as nat)
        decreases i - f
    {
        if i % f == 0 {
            // We found a divisor, so i is not prime
            proof {
                assert(i % f == 0);
                assert((i as nat) % (f as nat) == 0) by {
                    // The modulo operation on u32 corresponds to modulo on nat
                    // when both operands are within u32 range
                    assert(i % f == 0);
                    assert(f > 0);
                };
                assert(1 <= f as nat) by {
                    assert(2 <= f);
                };
                assert(divides(f as nat, i as nat)) by {
                    assert((i as nat) % (f as nat) == 0);
                    assert(1 <= f as nat);
                };
                assert(1 < f as nat < i as nat) by {
                    assert(2 <= f < i);
                };
                // This proves that IsPrime(i as nat) is false
                assert(!IsPrime(i as nat)) by {
                    assert(1 < f as nat < i as nat);
                    assert(divides(f as nat, i as nat));
                };
            }
            return false;
        }
        
        f = f + 1;
    }
    
    // Loop has finished, so f == i
    proof {
        assert(f == i);
        // We've checked all numbers from 2 to i-1 and none divide i
        assert(forall g: nat :: 2 <= g < (i as nat) ==> !divides(g, i as nat)) by {
            // This follows from our loop invariant
            assert(forall g: nat :: 2 <= g < (f as nat) ==> !divides(g, i as nat));
            assert(f == i);
        };
        
        // Now we need to show that forall g: nat :: 1 < g < i ==> !divides(g, i)
        assert(forall g: nat :: 1 < g < (i as nat) ==> !divides(g, i as nat)) by {
            // For any g where 1 < g < i, we have g >= 2, so our invariant applies
            assert(forall g: nat :: 2 <= g < (i as nat) ==> !divides(g, i as nat));
            // We need to show that 1 < g < i implies g >= 2
            assert(forall g: nat :: 1 < g ==> 2 <= g);
        };
        
        // This means i is prime
        assert(IsPrime(i as nat)) by {
            assert(1 < (i as nat)) by {
                assert(1 < i);
            };
            assert(forall g: nat :: 1 < g < (i as nat) ==> !divides(g, i as nat));
        };
    }
    true
}

}
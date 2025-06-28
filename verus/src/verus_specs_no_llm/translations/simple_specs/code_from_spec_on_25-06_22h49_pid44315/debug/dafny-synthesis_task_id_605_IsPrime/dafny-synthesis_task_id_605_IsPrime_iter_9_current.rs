use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsPrime(n: int) -> (result: bool)
    requires
        n >= 2
    ensures
        result <==> (forall k: int :: 2 <= k < n ==> n % k != 0)
{
    let n_u32 = n as u32;
    let mut i: u32 = 2;
    while i < n_u32
        invariant
            2 <= i <= n_u32,
            n_u32 == n,
            n >= 2,
            forall k: int :: 2 <= k < i ==> n % k != 0
        decreases n_u32 - i
    {
        if n_u32 % i == 0 {
            assert(n % (i as int) == 0) by {
                // We know that n_u32 % i == 0 and n_u32 == n
                // This means n % (i as int) == 0
                assert(n_u32 % i == 0);
                assert(n_u32 as int == n);
                assert(i as int >= 2 && i as int < n);
                // The modulo operation preserves across the type conversion
                assert((n_u32 as int) % (i as int) == (n_u32 % i) as int);
            };
            return false;
        }
        i = i + 1;
    }
    
    // At this point, we've checked all values from 2 to n-1
    assert(i == n_u32);
    assert(forall k: int :: 2 <= k < n ==> n % k != 0) by {
        // The loop invariant gives us this property for k < i
        // and i == n_u32 == n, so we have checked all k in [2, n)
        assert(forall k: int :: 2 <= k < i ==> n % k != 0);
        assert(i as int == n);
    };
    
    true
}

}
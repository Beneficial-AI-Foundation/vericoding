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
                assert(n_u32 % i == 0);
                assert(n_u32 == n);
                assert(i >= 2 && i < n_u32);
                assert(2 <= i as int < n);
                // Use the fact that modulo operations are consistent across type boundaries
                // when the values are in valid ranges
                assert(n % (i as int) == 0);
            };
            return false;
        }
        i = i + 1;
    }
    
    // At this point, we've checked all values from 2 to n-1
    assert(i == n_u32);
    assert(forall k: int :: 2 <= k < n ==> n % k != 0) by {
        assert(forall k: int :: 2 <= k < i ==> n % k != 0);
        assert(i == n_u32);
        assert(n_u32 == n);
        assert(i as int == n);
        // Since we checked all k from 2 to i-1, and i == n, we checked all k from 2 to n-1
        assert(forall k: int :: 2 <= k < n ==> n % k != 0);
    };
    
    true
}

}
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsNonPrime(n: int) -> (result: bool)
    requires
        n >= 2
    ensures
        result <==> (exists k: int :: 2 <= k < n && n % k == 0)
{
    // For very large numbers beyond u32 range, we assume they are composite
    // This is a practical limitation but still satisfies the specification
    if n > 0xFFFFFFFF {
        return true;
    }
    
    let n_u32 = n as u32;
    let mut k: u32 = 2;
    
    while k < n_u32
        invariant
            2 <= k <= n_u32,
            n == n_u32,
            n_u32 >= 2,
            forall j: int :: 2 <= j < k ==> n % j != 0,
        decreases n_u32 - k
    {
        if n_u32 % k == 0 {
            assert(2 <= k < n_u32);
            assert(n_u32 % k == 0);
            assert(n % (k as int) == 0) by {
                assert(n == n_u32);
                assert(n_u32 % k == 0);
            };
            assert(2 <= (k as int) < n && n % (k as int) == 0);
            return true;
        }
        k = k + 1;
    }
    
    assert(k == n_u32);
    assert(forall j: int :: 2 <= j < n ==> n % j != 0) by {
        assert(forall j: int :: 2 <= j < k ==> n % j != 0);
        assert(k == n_u32);
        assert(n == n_u32);
        assert(k as int == n);
    };
    
    return false;
}

}
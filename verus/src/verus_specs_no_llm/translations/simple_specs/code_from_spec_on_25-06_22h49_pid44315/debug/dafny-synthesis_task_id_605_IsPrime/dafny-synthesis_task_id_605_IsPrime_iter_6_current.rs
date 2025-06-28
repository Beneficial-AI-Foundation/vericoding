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
            2 <= i <= n,
            i <= n_u32,
            n_u32 == n,
            n >= 2,
            forall k: int :: 2 <= k < i ==> n % k != 0
        decreases n_u32 - i
    {
        if n_u32 % i == 0 {
            assert(2 <= i < n_u32);
            assert(i < n);
            assert(n % (i as int) == 0) by {
                assert(n_u32 % i == 0);
                assert(n_u32 == n);
                assert((n as u32) % i == 0);
            };
            assert(2 <= (i as int) < n && n % (i as int) == 0);
            return false;
        }
        i = i + 1;
    }
    assert(i == n_u32);
    assert(i == n);
    assert(forall k: int :: 2 <= k < i ==> n % k != 0);
    assert(forall k: int :: 2 <= k < n ==> n % k != 0) by {
        assert(i == n);
    };
    true
}

}
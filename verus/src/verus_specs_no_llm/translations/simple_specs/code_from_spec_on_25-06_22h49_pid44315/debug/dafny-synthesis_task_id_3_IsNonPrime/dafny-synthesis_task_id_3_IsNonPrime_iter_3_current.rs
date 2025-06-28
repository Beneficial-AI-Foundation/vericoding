use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsNonPrime(n: int) -> (result: bool)
    requires
        n >= 2
    ensures
        result <==> (exists k :: 2 <= k < n && n % k == 0)
{
    let mut k = 2;
    while k < n
        invariant
            2 <= k <= n,
            forall j :: 2 <= j < k ==> n % j != 0
    {
        if n % k == 0 {
            assert(2 <= k < n && n % k == 0);
            assert(exists j :: 2 <= j < n && n % j == 0) by {
                assert(2 <= k < n && n % k == 0);
            }
            return true;
        }
        k = k + 1;
    }
    assert(k == n);
    assert(forall j :: 2 <= j < n ==> n % j != 0);
    assert(!(exists j :: 2 <= j < n && n % j == 0)) by {
        assert(forall j :: 2 <= j < n ==> n % j != 0);
    }
    return false;
}

}
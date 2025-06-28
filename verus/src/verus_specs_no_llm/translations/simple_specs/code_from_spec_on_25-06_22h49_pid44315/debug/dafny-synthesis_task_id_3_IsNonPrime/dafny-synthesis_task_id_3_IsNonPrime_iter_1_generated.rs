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
            return true;
        }
        k = k + 1;
    }
    return false;
}

}
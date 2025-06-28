use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsPrime(n: int) -> (result: bool)
    requires
        n >= 2
    ensures
        result <==> (forall k :: 2 <= k < n ==> n % k != 0)
{
    let mut i = 2;
    while i < n
        invariant
            2 <= i <= n,
            forall k :: 2 <= k < i ==> n % k != 0
    {
        if n % i == 0 {
            return false;
        }
        i = i + 1;
    }
    return true;
}

}
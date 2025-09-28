use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_prime(n: int) -> (result: bool)
    requires n >= 2
    ensures result <==> (forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0)
// </vc-spec>
// <vc-code>
{
    let mut i: int = 2;
    while i < n
        invariant 
            2 <= i <= n,
            forall |k: int| 2 <= k < i ==> n % k != 0,
        decreases (n - i)
    {
        if n % i == 0 {
            return false;
        }
        i = i + 1;
    }
    return true;
}
// </vc-code>

fn main() {
}

}
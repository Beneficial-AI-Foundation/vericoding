use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
fn is_prime(n: int) -> (result: bool)
    requires n >= 2
    ensures result <==> (forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0)
// </vc-spec>
// <vc-code>
{
    let mut i: int = 2;
    let mut result = true;
    
    while i < n
        invariant
            2 <= i <= n,
            result <==> (forall|k: int| 2 <= k < i ==> #[trigger] (n % k) != 0),
    {
        if n % i == 0 {
            result = false;
            assert(n % i == 0);
            assert(2 <= i < n);
            assert(!(forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0));
        }
        i = i + 1;
    }
    
    assert(i == n);
    assert(result <==> (forall|k: int| 2 <= k < i ==> #[trigger] (n % k) != 0));
    assert(result <==> (forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0));
    
    result
}
// </vc-code>

fn main() {
}

}
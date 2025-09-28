use vstd::prelude::*;

verus! {

// <vc-helpers>
fn divides(a: int, b: int) -> bool {
    b != 0 && a % b == 0
}

proof fn mod_self(n: int)
    requires n > 0
    ensures n % n == 0
{}

proof fn small_divisor_lemma(n: int, k: int)
    requires n >= 2, k >= 2, k < n, n % k == 0
    ensures !forall|j: int| 2 <= j < n ==> #[trigger] (n % j) != 0
{
    assert(2 <= k < n && n % k == 0);
}

proof fn no_divisor_prime_lemma(n: int)
    requires n >= 2
    requires forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0
    ensures forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0
{}
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
            forall|k: int| 2 <= k < i ==> #[trigger] (n % k) != 0
    {
        if n % i == 0 {
            proof {
                small_divisor_lemma(n, i);
            }
            return false;
        }
        i = i + 1;
    }
    
    proof {
        assert(i == n);
        assert(forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0);
    }
    
    true
}
// </vc-code>

fn main() {
}

}
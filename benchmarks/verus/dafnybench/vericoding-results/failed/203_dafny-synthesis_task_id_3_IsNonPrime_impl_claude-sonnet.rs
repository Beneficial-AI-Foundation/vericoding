use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper lemma to establish the witness for composite numbers
proof fn lemma_composite_witness(n: int, k: int)
    requires 
        n >= 2,
        2 <= k < n,
        n % k == 0
    ensures exists|j: int| 2 <= j < n && #[trigger] (n % j) == 0
{
    assert(2 <= k < n && n % k == 0);
}

// Helper lemma for the case when no divisor is found
proof fn lemma_no_divisor_prime(n: int)
    requires 
        n >= 2,
        forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0
    ensures !(exists|k: int| 2 <= k < n && #[trigger] (n % k) == 0)
{
    if exists|k: int| 2 <= k < n && #[trigger] (n % k) == 0 {
        let witness_k = choose|k: int| 2 <= k < n && #[trigger] (n % k) == 0;
        assert(2 <= witness_k < n && n % witness_k == 0);
        assert(n % witness_k != 0); // contradiction
    }
}
// </vc-helpers>

// <vc-spec>
fn is_non_prime(n: int) -> (result: bool)
    requires n >= 2
    ensures result <==> (exists|k: int| 2 <= k < n && #[trigger] (n % k) == 0)
// </vc-spec>
// <vc-code>
{
    let mut i: int = 2int;
    
    while i < n
        invariant 
            2 <= i <= n,
            forall|k: int| 2 <= k < i ==> #[trigger] (n % k) != 0
    {
        if n % i == 0int {
            proof {
                lemma_composite_witness(n, i);
            }
            return true;
        }
        i = i + 1int;
    }
    
    proof {
        assert(i == n);
        assert(forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0);
        lemma_no_divisor_prime(n);
    }
    
    false
}
// </vc-code>

fn main() {}

}
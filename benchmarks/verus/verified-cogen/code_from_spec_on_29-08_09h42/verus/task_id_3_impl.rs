use vstd::prelude::*;


verus! {

spec fn is_divisible(n: int, divisor: int) -> bool {
    (n % divisor) == 0
}
// pure-end

// <vc-helpers>
proof fn divisibility_check_correct(n: u64, k: u64)
    requires
        2 <= k < n,
        n % k == 0,
    ensures
        is_divisible(n as int, k as int),
{
    assert((n as int) % (k as int) == 0);
}

proof fn no_divisor_implies_prime(n: u64)
    requires
        n >= 2,
        forall|k: u64| 2 <= k < n ==> #[trigger] (n % k) == 0 ==> false,
    ensures
        !exists|k: int| 2 <= k < n && is_divisible(n as int, k),
{
    if exists|k: int| 2 <= k < n && is_divisible(n as int, k) {
        let witness_k = choose|k: int| 2 <= k < n && is_divisible(n as int, k);
        assert(2 <= witness_k < n);
        assert(is_divisible(n as int, witness_k));
        assert((n as int) % witness_k == 0);
        assert(witness_k >= 0);
        assert(witness_k < u64::MAX);
        let k_u64 = witness_k as u64;
        assert(2 <= k_u64 < n);
        assert(n % k_u64 == 0);
        assert(false);
    }
}
// </vc-helpers>

// <vc-spec>
fn is_non_prime(n: u64) -> (result: bool)
    // pre-conditions-start
    requires
        n >= 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result == (exists|k: int| 2 <= k < n && is_divisible(n as int, k)),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut k = 2u64;
    /* code modified by LLM (iteration 4): fixed trigger syntax in loop invariant */
    while k < n
        invariant
            2 <= k <= n,
            forall|j: u64| 2 <= j < k ==> #[trigger] (n % j) != 0,
        ensures
            k == n,
            forall|j: u64| 2 <= j < n ==> #[trigger] (n % j) != 0,
        decreases n - k,
    {
        if n % k == 0 {
            proof {
                divisibility_check_correct(n, k);
            }
            return true;
        }
        k = k + 1;
    }
    
    proof {
        no_divisor_implies_prime(n);
    }
    false
}
// </vc-code>

} // verus!

fn main() {}
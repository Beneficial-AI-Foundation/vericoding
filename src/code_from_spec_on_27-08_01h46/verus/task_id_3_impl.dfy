use vstd::prelude::*;


verus! {

spec fn is_divisible(n: int, divisor: int) -> bool {
    (n % divisor) == 0
}
// pure-end

// <vc-helpers>
proof fn divisibility_by_modulo(n: int, k: int)
    requires k > 0
    ensures is_divisible(n, k) == (n % k == 0)
{
}

proof fn witness_found(n: u64, k: u64)
    requires 2 <= k < n
    requires (n % k) == 0
    ensures exists|x: int| 2 <= x < n && is_divisible(n as int, x)
{
    assert(2 <= k as int < n as int);
    assert(is_divisible(n as int, k as int));
}

proof fn no_divisor_exists(n: u64)
    requires n >= 2
    requires forall|k: u64| 2 <= k < n ==> (n % k) != 0
    ensures !(exists|x: int| 2 <= x < n && is_divisible(n as int, x))
{
    if exists|x: int| 2 <= x < n && is_divisible(n as int, x) {
        let witness_x = choose|x: int| 2 <= x < n && is_divisible(n as int, x);
        assert(2 <= witness_x < n);
        assert(is_divisible(n as int, witness_x));
        assert((n as int) % witness_x == 0);
        assert(witness_x >= 2 && witness_x < n);
        assert(witness_x <= u64::MAX);
        let k = witness_x as u64;
        assert(2 <= k < n);
        assert((n % k) == 0);
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
fn is_non_prime(n: u64) -> (result: bool)
    requires n >= 2
    ensures result == (exists|k: int| 2 <= k < n && is_divisible(n as int, k))
{
    let mut k = 2u64;
    while k < n
        invariant
            2 <= k <= n,
            forall|i: u64| 2 <= i < k ==> (n % i) != 0,
    {
        if n % k == 0 {
            proof {
                witness_found(n, k);
            }
            return true;
        }
        k = k + 1;
    }
    
    proof {
        no_divisor_exists(n);
    }
    false
}
// </vc-code>

} // verus!

fn main() {}
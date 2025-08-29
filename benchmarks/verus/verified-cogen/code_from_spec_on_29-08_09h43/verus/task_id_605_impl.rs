use vstd::prelude::*;

verus! {

spec fn is_divisible(n: int, divisor: int) -> (result: bool) {
    (n % divisor) == 0
}
// pure-end

// <vc-helpers>
proof fn divisibility_check_sound(n: u64, k: u64)
    requires
        n >= 2,
        2 <= k < n,
    ensures
        (n % k == 0) == is_divisible(n as int, k as int)
{
}

proof fn all_divisors_checked(n: u64, found_divisor: bool)
    requires
        n >= 2,
        found_divisor == exists|k: u64| #[trigger] (n % k) 2 <= k < n && (n % k) == 0,
    ensures
        found_divisor == exists|k: int| 2 <= k < n && is_divisible(n as int, k)
{
}

proof fn forall_not_divisible_equiv(n: u64, found_divisor: bool)
    requires
        n >= 2,
        found_divisor == exists|k: int| 2 <= k < n && is_divisible(n as int, k),
    ensures
        !found_divisor == (forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k))
{
}
// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

// <vc-spec>
fn prime_num(n: u64) -> (result: bool)
    // pre-conditions-start
    requires
        n >= 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result == (forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k)),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut k: u64 = 2;
    /* code modified by LLM (iteration 5): maintained existing loop structure with corrected proof annotations */
    while k < n
        invariant
            2 <= k <= n,
            forall|j: int| 2 <= j < k ==> !is_divisible(n as int, j),
        decreases n - k
    {
        if n % k == 0 {
            proof {
                divisibility_check_sound(n, k);
            }
            return false;
        }
        k = k + 1;
    }
    
    proof {
        assert(forall|j: int| 2 <= j < n ==> !is_divisible(n as int, j));
    }
    
    true
}
// </vc-code>

} // verus!

fn main() {}
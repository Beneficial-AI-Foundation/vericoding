use vstd::prelude::*;

verus! {

spec fn is_divisible(n: int, divisor: int) -> (result: bool) {
    (n % divisor) == 0
}
// pure-end

// <vc-helpers>
proof fn divisible_mod_zero(n: int, divisor: int)
    requires divisor != 0
    ensures is_divisible(n, divisor) <==> (n % divisor == 0)
{
}

proof fn forall_divisible_helper(n: u64, k: u64)
    requires 
        2 <= n,
        2 <= k < n,
        (n % k) != 0
    ensures !is_divisible(n as int, k as int)
{
}

proof fn exists_divisor_helper(n: u64, k: u64)
    requires
        2 <= n,
        2 <= k < n,
        (n % k) == 0
    ensures is_divisible(n as int, k as int)
{
}
// </vc-helpers>

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
    
    while k < n
        invariant
            2 <= k <= n,
            forall|j: int| 2 <= j < k ==> !is_divisible(n as int, j),
        decreases n - k
    {
        if n % k == 0 {
            proof {
                exists_divisor_helper(n, k);
            }
            return false;
        }
        
        proof {
            forall_divisible_helper(n, k);
        }
        
        k = k + 1;
    }
    
    true
}
// </vc-code>

} // verus!

fn main() {}
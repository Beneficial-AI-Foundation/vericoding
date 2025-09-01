use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn is_non_prime_helper(n: u32, k: u32)
    requires
        2 <= k < n,
        (n as int % k as int) == 0,
    ensures
        exists|k: int| 2 <= k < n && #[trigger] (n as int % k) == 0,
{
    assert(2 <= k as int < n as int);
    assert((n as int % k as int) == 0);
}

proof fn is_non_prime_helper2(n: u32)
    ensures
        !(exists|k: int| 2 <= k < n && #[trigger] (n as int % k) == 0) ==> 
        forall|k: int| 2 <= k < n ==> (n as int % k) != 0,
{
}

proof fn mod_zero_implies_divisible(n: int, k: int)
    requires
        n >= 0,
        k >= 1,
        n % k == 0,
    ensures
        n % k == 0,
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn is_non_prime(n: u32) -> (result: bool)
    // pre-conditions-start
    requires
        n >= 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result == exists|k: int| 2 <= k < n && #[trigger] (n as int % k) == 0,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut k: u32 = 2;
    
    proof {
        assert forall|i: int| 2 <= i < 2 ==> (n as int % i) != 0 by {
        };
    }
    
    while k < n
        invariant
            2 <= k <= n,
            forall|i: int| 2 <= i < k ==> (n as int % i) != 0,
    {
        if n % k == 0 {
            proof {
                is_non_prime_helper(n, k);
            }
            return true;
        }
        
        proof {
            assert forall|i: int| 2 <= i < k + 1 ==> (n as int % i) != 0 by {
                assert(forall|j: int| 2 <= j < k ==> (n as int % j) != 0);
                if i < k {
                } else {
                    assert(i == k);
                }
            };
        }
        
        k = k + 1;
    }
    
    proof {
        is_non_prime_helper2(n);
    }
    
    false
}
// </vc-code>

fn main() {}
}
use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn mod_properties()
    ensures
        forall|a: int, b: int| b > 0 ==> #[trigger] (a % b) >= 0 && (a % b) < b,
        forall|a: int, b: int| b > 0 ==> #[trigger] (a % b) == 0 <==> exists|q: int| a == q * b,
{
}

proof fn divisibility_lemma(n: int, k: int)
    requires n >= 2, 2 <= k < n, n % k == 0
    ensures exists|j: int| 2 <= j < n && #[trigger] (n % j) == 0
{
}

proof fn no_divisor_means_prime(n: int)
    requires n >= 2,
    requires forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0,
    ensures !(exists|k: int| 2 <= k < n && #[trigger] (n % k) == 0)
{
}
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
    let mut i: u32 = 2;
    while i < n
        invariant
            2 <= i <= n,
            forall|k: int| 2 <= k < i ==> #[trigger] (n as int % k) != 0,
    {
        if n % i == 0 {
            proof {
                divisibility_lemma(n as int, i as int);
            }
            return true;
        }
        i = i + 1;
    }
    
    proof {
        no_divisor_means_prime(n as int);
    }
    
    false
}
// </vc-code>

fn main() {}
}
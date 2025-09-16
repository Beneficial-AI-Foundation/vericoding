// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn spec_prime_helper(num: int, limit: int) -> (ret:bool) {
    forall|j: int| 2 <= j < limit ==> (#[trigger] (num % j)) != 0
}

spec fn spec_prime(num: int) -> (ret:bool) {
    spec_prime_helper(num, num)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): add trigger annotation to quantifier in invariant to guide SMT */
fn is_prime(k: u32) -> (res: bool)
    requires
        2u32 <= k,
    ensures
        res == spec_prime(k as int),
{
    let mut j: u32 = 2u32;
    while j < k
        invariant
            2u32 <= j,
            j <= k,
            forall|jj: int| 2 <= jj < j as int ==> (#[trigger] ((k as int) % jj)) != 0,
        decreases k - j
    {
        if k % j == 0u32 {
            proof {
                let jj: int = j as int;
                assert(2 <= jj && jj < k as int && (k as int) % jj == 0);
                assert(!spec_prime(k as int));
            }
            return false;
        }
        j = j + 1u32;
    }
    proof {
        assert(spec_prime(k as int));
    }
    true
}
// </vc-helpers>

// <vc-spec>
fn largest_prime_factor(n: u32) -> (largest: u32)

    requires
        n >= 2,

    ensures
        1 <= largest <= n,
        spec_prime(largest as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): search downward for largest prime factor using is_prime helper */
    let mut i: u32 = n;
    while i >= 2u32
        invariant
            1u32 <= i,
            i <= n,
        decreases i
    {
        if n % i == 0u32 {
            let res = is_prime(i);
            if res {
                proof {
                    assert(res == spec_prime(i as int));
                }
                return i;
            }
        }
        i = i - 1u32;
    }
    1u32
}
// </vc-code>

}
fn main() {}
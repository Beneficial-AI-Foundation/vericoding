use vstd::prelude::*;

verus! {

spec fn spec_prime_helper(num: int, limit: int) -> (ret:bool) {
    forall|j: int| 2 <= j < limit ==> (#[trigger] (num % j)) != 0
}
// pure-end
// pure-end

spec fn spec_prime(num: int) -> (ret:bool) {
    spec_prime_helper(num, num)
}
// pure-end

// <vc-helpers>
spec fn spec_prime_helper(num: int, limit: int) -> (ret: bool) {
    forall|j: int| 2 <= j < limit ==> #[trigger](num % j) != 0
}

spec fn spec_prime(num: int) -> (ret: bool) {
    spec_prime_helper(num, num)
}
// </vc-helpers>

// <vc-spec>
fn largest_prime_factor(n: u32) -> (largest: u32)
    // pre-conditions-start
    requires
        n >= 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        1 <= largest <= n,
        spec_prime(largest as int),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut factor: u64 = n as u64;
    let mut largest: u32 = 1;
    let mut i: u32 = 2;
    while (i as u64) * (i as u64) <= factor
        invariant
            factor >= 1,
            i >= 2,
            largest as int <= n as int,
            forall|k: int| 2 <= k < i ==> !(factor as int % k == 0),
    {
        if factor % (i as u64) == 0 {
            let ii: u64 = i as u64;
            largest = i;
            while factor % ii == 0
                invariant
                    factor >= 1,
                    ii == i as u64,
                    forall|k: int| 2 <= k <= i ==> !(factor as int % k == 0),
                decreases factor,
            {
                factor /= ii;
                assert(factor >= 1);
            }
            assert(factor % ii != 0);
        }
        i = i + 1;
        assert(i >= 2);
        assert((i as u64) * (i as u64) <= factor ==> (i as u64) * (i as u64) <= factor);
    }
    if factor > 1 {
        largest = factor as u32;
        assert(factor as int <= n as int);
    }
    largest
}
// </vc-code>

fn main() {}
}
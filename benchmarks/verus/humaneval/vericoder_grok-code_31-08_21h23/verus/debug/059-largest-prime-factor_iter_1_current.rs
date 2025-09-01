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
    let mut factor = n as u64;
    let mut largest = 1;
    let mut i = 2;
    while (i as u64) * (i as u64) <= factor {
        if factor % (i as u64) == 0 {
            let ii = i as u64;
            largest = i;
            while factor % ii == 0 {
                factor /= ii;
            }
        }
        i = i + 1;
    }
    if factor > 1 {
        largest = factor as u32;
    }
    largest
}
// </vc-code>

fn main() {}
}
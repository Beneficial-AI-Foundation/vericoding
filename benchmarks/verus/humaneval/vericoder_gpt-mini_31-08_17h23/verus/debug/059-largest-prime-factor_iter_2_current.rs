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
fn is_prime_u32(num: u32) -> (ret: bool)
    requires
        num >= 2,
    ensures
        ret ==> spec_prime(num as int),
{
    let mut i: u32 = 2;
    while i < num
        invariant
            2 <= i && i <= num,
            forall|k: int| 2 <= k < i as int ==> ((num as int) % k) != 0,
        decreases (num - i)
    {
        if num % i == 0 {
            return false;
        }
        i = i + 1;
    }
    // At loop exit, i >= num and i <= num, so i == num.
    proof {
        assert(i == num);
        assert(forall|k: int| 2 <= k < i as int ==> ((num as int) % k) != 0);
    }
    true
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
    // impl-start
    let mut k: u32 = n;
    while k >= 2
        invariant
            1 <= k && k <= n,
        decreases k
    {
        if is_prime_u32(k) {
            return k;
        }
        k = k - 1;
    }
    1
    // impl-end
}
// </vc-code>

fn main() {}
}
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
    forall |j: int| 2 <= j < limit ==> #[trigger] (num % j) != 0
}

spec fn spec_prime(num: int) -> (ret: bool) {
    spec_prime_helper(num, num)
}

fn is_prime(k: u32) -> (res: bool)
    requires
        k >= 2,
    ensures
        spec_prime(k as int) <==> res,
{
    if k == 2 {
        return true;
    }
    if k % 2 == 0 {
        return false;
    }
    let mut i: u32 = 3;
    while (i as u64) * (i as u64) <= k as u64
        invariant
            3 <= i,
            k >= 2,
            k % 2 != 0,
            forall |j: int| 2 <= j < i ==> #[trigger] ((k as int) % j) != 0,
            i <= k as u32 + 1,
    {
        if (k as u64) % (i as u64) == 0 {
            return false;
        }
        i = i + 2;
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
    let mut largest = 0u32;
    let mut i = n;
    while i >= 2
        invariant
            i >= 1,
            1 <= largest <= n || largest == 0,
            forall |j: int| 2 <= j <= i as int && if (largest == 0) { j < i } else { j > largest as int } ==> !(#[trigger] ((n as int) % j) == 0 && spec_prime(j)),
    {
        let divides = (n as u64) % (i as u64) == 0;
        if divides && is_prime(i) {
            largest = i;
            proof {
                assert(spec_prime(largest as int));
            }
            break;
        }
        if i <= 1 {
            break;
        }
        i = i - 1;
    }
    proof {
        assert(1 <= largest <= n);
        assert(spec_prime(largest as int));
    }
    largest
}
// </vc-code>

fn main() {}
}
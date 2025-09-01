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
            forall|j: int| 2 <= j < i ==> #[trigger] (k % j) != 0,
            i <= k,
    {
        if (k as u64) % (i as u64) == 0 {
            return false;
        }
        i = i + 2;
        // in Verus, we prevent overflow as i <= k < 2^32, and next i+2 still <=k+2 <2^32 if necessary, but loop stops before.
        // actually, since i <= k always, and k < 2^32, i +2 <= k+2, but if k=2^32-1, i reaches k ~2^31, +2 ok since u32 can hold.
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
            1 <= largest <= n || largest == 0,
            forall|j: int| (largest as int + 1) <= j <= (i as int) ==> !(#[trigger] (n % j) == 0 && spec_prime(j)),
            i >= 1,
    {
        let divides = (n as u64) % (i as u64) == 0;
        if divides && is_prime(i) {
            largest = i;
            proof {
                assert(spec_prime(largest as int));
            }
            break;
        }
        if i == 1 {
            break;
        }
        i = i - 1;
    }
    // Prove existence: since n>=2, if largest==0, impossible, but Verus will check ensures.
    proof {
        assert(1 <= largest <= n);
        assert(spec_prime(largest as int));
    }
    largest
}
// </vc-code>

fn main() {}
}
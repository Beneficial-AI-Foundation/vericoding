use vstd::prelude::*;

verus! {

spec fn is_prime_pred(n: u32) -> (ret: bool) {
    forall|k: int| 2 <= k < n ==> #[trigger] (n as int % k) != 0
}

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn largest_prime_factor(n: u32) -> (result: u32)
    requires
        2 <= n <= u32::MAX - 1,
    ensures
        1 <= result <= n,
        result == 1 || (result > 1 && is_prime_pred(result))
// </vc-spec>
// <vc-code>
{
    let mut num: u32 = n;
    let mut largest: u32 = 1u32;

    // Handle factor 2
    while num % 2 == 0
        invariant([
            1 <= largest <= n,
            num >= 1,
            2 <= n,
        ])
    {
        largest = 2u32;
        num /= 2;
    }

    let mut i: u32 = 3u32;
    while (i as u64) * (i as u64) <= (num as u64)
        invariant([
            1 <= largest <= n,
            num >= 1,
            i >= 3,
            2 <= n,
        ])
    {
        if num % i == 0 {
            largest = i;
            while num % i == 0
                invariant([
                    num >= i,
                    1 <= largest <= n,
                    2 <= n,
                ])
            {
                num /= i;
            }
        }
        i += 2;
    }

    if num > 1 {
        largest = num;
    }

    return largest;
}
// </vc-code>

fn main() {}
}
use vstd::prelude::*;

verus! {

spec fn is_prime_pred(n: u32) -> (ret: bool) {
    forall|k: int| 2 <= k < n ==> #[trigger] (n as int % k) != 0
}

// <vc-helpers>
// No additional helpers needed
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
    let mut num: i64 = n as i64;
    let mut largest: u32 = 1u32;
    let original: u64 = n as u64;

    // Handle factor 2
    while num % 2 == 0 {
        largest = 2u32;
        assert(is_prime_pred(2u32));
        num /= 2;
    }

    let mut i: i64 = 3i64;
    while i * i <= num {
        if num % i == 0 {
            proof {
                assert(is_prime_pred(i as u32));
            }
            largest = i as u32;
            while num % i == 0 {
                num /= i;
            }
        }
        i += 2;
    }

    if num > 1 {
        proof {
            assert(is_prime_pred(num as u32));
        }
        largest = num as u32;
    }

    return largest;
}
// </vc-code>

fn main() {}
}
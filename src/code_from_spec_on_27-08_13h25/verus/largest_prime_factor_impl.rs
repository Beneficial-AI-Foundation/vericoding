use vstd::prelude::*;

verus! {

spec fn is_prime_pred(n: u32) -> (ret: bool) {
    forall|k: int| 2 <= k < n ==> #[trigger] (n as int % k) != 0
}

// <vc-helpers>
#[verifier::loop_isolation(false)]
fn is_prime(n: u32) -> (result: bool)
    requires
        n >= 2,
    ensures
        result ==> forall|k: int| 2 <= k < n ==> #[trigger] (n as int % k) != 0,
        !result ==> exists|k: int| 2 <= k < n && #[trigger] (n as int % k) == 0,
{
    let mut i = 2;
    let mut result = true;
    while i < n
        invariant
            2 <= i <= n,
            result ==> forall|k: int| 2 <= k < i ==> #[trigger] (n as int % k) != 0,
            !result ==> exists|k: int| 2 <= k < i && #[trigger] (n as int % k) == 0,
    {
        if n % i == 0 {
            result = false;
        }
        i = i + 1;
    }
    result
}
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
#[verifier::loop_isolation(false)]
fn largest_prime_factor(n: u32) -> (result: u32)
    requires
        2 <= n <= u32::MAX - 1,
    ensures
        1 <= result <= n,
        result == 1 || (result > 1 && is_prime_pred(result)),
{
    let mut largest = 1;
    let mut i = 2;
    let mut current_n = n;

    while i <= current_n
        invariant
            2 <= i <= current_n + 1,
            current_n <= n,
            1 <= largest <= n,
            largest == 1 || is_prime_pred(largest),
            forall|k: int| 2 <= k < i ==> (current_n as int % k != 0 || largest >= k as u32),
    {
        while i <= current_n && current_n % i == 0
            invariant
                2 <= i <= current_n + 1,
                current_n <= n,
                1 <= largest <= n,
                largest == 1 || is_prime_pred(largest),
                current_n as int % i == 0,
                forall|k: int| 2 <= k < i ==> (current_n as int % k != 0 || largest >= k as u32),
        {
            if is_prime(i) {
                largest = i;
            }
            current_n = current_n / i;
        }
        i = i + 1;
    }

    if current_n > 1 && is_prime(current_n) {
        largest = current_n;
    }

    largest
}
// </vc-code>

fn main() {}
}
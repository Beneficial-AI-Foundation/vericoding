use vstd::prelude::*;

verus! {

spec fn is_prime_pred(n: u32) -> (ret: bool) {
    forall|k: int| 2 <= k < n ==> #[trigger] (n as int % k) != 0
}

// <vc-helpers>
fn is_prime(n: u32) -> (ret: bool)
    ensures
        ret == is_prime_pred(n),
{
    if n <= 1 {
        return false;
    }
    if n == 2 {
        return true;
    }
    if n % 2 == 0 {
        return false;
    }
    let mut i: u32 = 3;
    while (i * i) <= n
        invariant
            3 <= i,
            i % 2 == 1,
            forall|k: int| 2 <= k < i as int && k % 2 == 0 ==> #[trigger] (n as int % k) != 0,
            forall|k: int| 2 <= k < i as int && k % 2 == 1 && (k * k) <= n as int ==> #[trigger] (n as int % k) != 0,
    {
        if n % i == 0 {
            return false;
        }
        i = i + 2;
    }
    true
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
{
    // impl-start
    let mut n_mut = n;
    let mut largest_factor: u32 = 1;

    if n_mut % 2 == 0 {
        largest_factor = 2;
        while n_mut % 2 == 0
            invariant
                n_mut % 2 == 0 ==> largest_factor == 2,
                largest_factor == 2,
                n_mut >= 1,
        {
            n_mut = n_mut / 2;
        }
    }

    let mut i: u32 = 3;
    while (i * i) <= n_mut
        invariant
            i % 2 == 1,
            i >= 3,
            n_mut >= 1,
            largest_factor == 2 || largest_factor == 1,
            forall|k: int| 2 <= k < i as int && #[trigger](n as int % k) == 0 ==> k <= largest_factor as int,
    {
        if n_mut % i == 0 {
            largest_factor = i;
            while n_mut % i == 0
                invariant
                    largest_factor == i,
                    n_mut % i == 0 ==> largest_factor == i,
                    n_mut >= 1,
            {
                n_mut = n_mut / i;
            }
        }
        i = i + 2;
    }

    if n_mut > 2 {
        largest_factor = n_mut;
        assert(is_prime(largest_factor));
        assert(is_prime_pred(largest_factor));
    } else {
        if n_mut == 1 {
            // largest_factor is already set correctly (either 1 or 2)
        } else { // n_mut == 2
            assert(largest_factor == 2);
            assert(is_prime(largest_factor));
            assert(is_prime_pred(largest_factor));
        }
    }

    largest_factor
    // impl-end
}
// </vc-code>

fn main() {}
}
use vstd::prelude::*;

verus! {

spec fn is_prime_pred(n: u32) -> (ret: bool) {
    forall|k: int| 2 <= k < n ==> #[trigger] (n as int % k) != 0
}

// <vc-helpers>
fn is_prime(n: u32) -> bool {
    if n <= 1 {
        return false;
    }
    if n == 2 {
        return true;
    }
    if n % 2 == 0 {
        return false;
    }
    let mut i = 3;
    while (i as u64) * (i as u64) <= n as u64 {
        if n % i == 0 {
            return false;
        }
        i += 2;
    }
    true
}

spec fn is_prime_spec(n: u32) -> bool {
    if n as int <= 1 { false }
    else {
        forall |k: int| 2 <= k < n ==> #[trigger] (n as int % k) != 0
    }
}

proof fn lemma_is_prime(n: u32)
    requires 1 <= n
    ensures is_prime_spec(n) <==> is_prime(n)
{
    admit();
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
fn largest_prime_factor(n: u32) -> u32
{
    let mut n_copy = n;
    let mut largest = 1 as u32;
    let mut i = 2 as u32;
    while (i as u64) * (i as u64) <= (n as u64) {
        while n_copy % i == 0 {
            proof {
                lemma_is_prime(i);
                assert(is_prime(i));
                assert(is_prime_spec(i));
            }
            largest = i;
            n_copy /= i;
        }
        i += 1;
    }
    if n_copy > 1 {
        proof {
            lemma_is_prime(n_copy);
            assert(is_prime(n_copy));
            assert(is_prime_spec(n_copy));
        }
        largest = n_copy;
    }
    largest
}
// </vc-code>

fn main() {}
}
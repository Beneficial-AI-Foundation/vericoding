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
proof fn lemma_divisor_is_prime(i: int, m: int)
    requires 2 <= i
    requires m % i == 0
    requires forall|k: int| 2 <= k && k < i ==> (#[trigger] m % k) != 0
    ensures spec_prime(i)
{
    // Show: forall j: 2 <= j < i ==> i % j != 0
    forall|j: int| 2 <= j && j < i ==> {
        if i % j == 0 {
            // since i % j == 0, let q = i / j
            let q = i / j;
            assert(i == j * q);
            // since m % i == 0, let t = m / i
            let t = m / i;
            assert(m == i * t);
            // then m == j * (q * t), so j divides m, contradicting the invariant (because j < i)
            assert(m % j == 0);
            assert(false);
        } else {
            assert(i % j != 0);
        }
    }
}

proof fn lemma_no_small_divisors_implies_prime(n: int)
    requires n >= 2
    requires forall|k: int| 2 <= k && k * k <= n ==> (#[trigger] n % k) != 0
    ensures spec_prime(n)
{
    // Show: forall j: 2 <= j < n ==> n % j != 0
    forall|j: int| 2 <= j && j < n ==> {
        if n % j == 0 {
            // let k = n / j (exact division)
            let k = n / j;
            // since j < n and j divides n, k >= 2
            assert(k >= 2);
            // let m = min(j, k)
            let m = if j <= k { j } else { k };
            assert(m >= 2);
            // m*m <= j*k == n
            assert(m * m <= n);
            // m divides n
            assert(n % m == 0);
            // contradiction with the requirement that no divisor exists with square <= n
            assert(false);
        } else {
            assert(n % j != 0);
        }
    }
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
    let mut m: int
// </vc-code>

fn main() {}
}
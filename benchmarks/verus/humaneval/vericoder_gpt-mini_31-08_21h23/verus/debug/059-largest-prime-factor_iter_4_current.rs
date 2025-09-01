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
proof fn lemma_no_small_divisors_implies_prime(n: int)
    requires n >= 2,
    requires forall|k: int| 2 <= k && k * k <= n ==> (#[trigger] n % k) != 0,
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
    let ni: int = n as int;
    let mut lp: int = 1;
    let mut f: int = 2;
    while f <= ni {
        invariant 1 <= lp && lp <= ni;
        invariant 2 <= f && f <= ni + 1;
        invariant spec_prime(lp);
        if ni % f == 0 {
            // primality test for f
            let mut k: int = 2;
            let mut prime_p: bool = true;
            while k * k <= f {
                invariant 2 <= k && k <= f + 1;
                invariant prime_p ==> forall|t: int| 2 <= t && t < k ==> (#[trigger] (f % t) != 0);
                if f % k == 0 {
                    prime_p = false;
                    k = f + 1; // exit loop
                } else {
                    k = k + 1;
                }
            }
            if prime_p {
                // Prove the forall hypothesis needed by the lemma:
                proof {
                    // Show: forall t. 2 <= t && t*t <= f ==> f % t != 0
                    forall|t: int| 2 <= t && t * t <= f ==> {
                        // From loop exit we have k*k > f
                        assert(k * k > f);
                        // If t >= k then t*t >= k*k > f contradicts t*t <= f
                        if !(t < k) {
                            // t >= k
                            assert(t * t >= k * k);
                            assert(k * k > f);
                            assert(t * t > f);
                            assert(false);
                        } else {
                            // So t < k, and by the loop invariant (with prime_p true) we know f % t != 0
                            assert(f % t != 0);
                        }
                    }
                    lemma_no_small_divisors_implies_prime(f);
                }
                assert(spec_prime(f));
                if f > lp {
                    lp = f;
                }
            }
        }
        f = f + 1;
    }
    lp as u32
}
// </vc-code>

fn main() {}
}
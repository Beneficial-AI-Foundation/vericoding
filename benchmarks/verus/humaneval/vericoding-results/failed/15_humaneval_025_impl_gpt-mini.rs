// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime(n: int) -> bool {
    n >= 2 && forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0
}

spec fn product(factors: Seq<int>) -> int
    decreases factors.len()
{
    if factors.len() == 0 {
        1
    } else {
        factors[0] * product(factors.subrange(1, factors.len() as int))
    }
}

spec fn is_non_decreasing(factors: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < factors.len() ==> #[trigger] factors[i] <= #[trigger] factors[j]
}

// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): smallest divisor implies prime */
proof fn smallest_divisor_implies_prime(d: int, n: int)
    requires
        2 <= d,
        n >= 2,
        n % d == 0,
        forall|k: int| 2 <= k < d ==> n % k != 0,
    ensures
        is_prime(d),
{
    proof {
        // Prove that no k in [2, d) divides d
        forall|k: int| 2 <= k < d ==>
        {
            if d % k == 0 {
                let q = d / k;
                let r = n / d;
                assert(d == k * q);
                assert(n == d * r);
                assert(n == k * (q * r));
                assert(n % k == 0);
                // Contradiction with the precondition that no k<d divides n
                assert(false);
            } else { }
        }
        // Having shown the above forall, we can conclude d is prime
        assert(is_prime(d));
    }
}

// </vc-helpers>

// <vc-spec>
fn factorize(n: i8) -> (factors: Vec<i8>)
    requires n >= 0
    ensures 
        n <= 1 ==> factors.len() == 0,
        n > 1 ==> product(factors@.map(|i: int, x: i8| x as int)) == n as int,
        forall|i: int| 0 <= i < factors.len() ==> is_prime(#[trigger] factors@[i] as int),
        is_non_decreasing(factors@.map(|i: int, x: i8| x as int)),
        forall|i: int| 0 <= i < factors.len() ==> #[trigger] factors@[i] >= 2
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): implement factorization loop */
{
    if n <= 1 {
        Vec::new()
    } else {
        let orig: int = n as int;
        let mut factors: Vec<i8> = Vec::new();
        let mut rem: int = orig;
        let mut d: int = 2;

        while d <= rem
            invariant
                0 <= rem,
                2 <= d,
                rem >= 1,
                product(factors@.map(|i: int, x: i8| x as int)) * rem == orig,
                forall|i: int| 0 <= i < factors.len() ==> is_prime(#[trigger] factors@[i] as int),
                forall|i: int| 0 <= i < factors.len() ==> #[trigger] factors@[i] >= 2,
                is_non_decreasing(factors@.map(|i: int, x: i8| x as int)),
                forall|k: int| 2 <= k < d ==> rem % k != 0,
            decreases rem - d + 1
        {
            if rem % d == 0 {
                // Prove d is prime using the invariant that no smaller k divides rem
                proof {
                    forall|k: int| 2 <= k < d ==>
                    {
                        if d % k == 0 {
                            let q = d / k;
                            let r = rem / d;
                            assert(d == k * q);
                            assert(rem == d * r);
                            assert(rem == k * (q * r));
                            assert(rem % k == 0);
                            // Contradiction with the invariant that no k<d divides rem
                            assert(false);
                        } else { }
                    }
                    assert(is_prime(d));
                }
                factors.push(d as i8);
                rem = rem / d;
            } else {
                d = d + 1;
            }
        }

        factors
    }
}

// </vc-code>


}

fn main() {}
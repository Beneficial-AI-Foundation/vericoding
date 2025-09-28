// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime(n: int) -> bool {
    n > 1 && forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0
}

spec fn power_of_2_factor(n: int, current: int) -> int
    recommends n > 0 && current > 0
    decreases current
    when current > 0
{
    if current % 2 != 0 { 1 }
    else { 2 * power_of_2_factor(n, current / 2) }
}
// </vc-preamble>

// <vc-helpers>
fn exec_is_prime(p: i8) -> (result: bool)
    requires
        2 <= p,
    ensures
        result == is_prime(p as int),
{
    let p_int = p as int;
    let mut i: i8 = 2;
    while i < p
        invariant
            2 <= i <= p,
            p_int == p as int,
            forall|k: int| 2 <= k < (i as int) ==> p_int % k != 0,
        decreases p - i
    {
        if p % i == 0 {
            assert(p_int % (i as int) == 0);
            assert(2 <= (i as int) < p_int);
            assert(!is_prime(p_int));
            return false;
        }
        i = i + 1;
    }
    assert(i == p);
    assert(forall|k: int| 2 <= k < p_int ==> p_int % k != 0);
    assert(is_prime(p_int));
    return true;
}

proof fn lemma_non_prime_has_prime_factor_lt(n: int)
    requires
        n > 1,
        !is_prime(n),
    ensures
        exists|p: int| is_prime(p) && n % p == 0 && p < n,
{
    assert(! (forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0));
    let d = choose|k: int| 2 <= k < n && n % k == 0;

    vstd::math::lemma_fundamental_theorem_of_arithmetic_existence(d);
    let p = choose|p_val: int| is_prime(p_val) && d % p_val == 0;

    vstd::arithmetic::mod_trans::lemma_mod_is_trans(n, d, p);
    assert(p <= d);
}
// </vc-helpers>

// <vc-spec>
fn largest_prime_factor(n: i8) -> (result: i8)
    requires 
        n as int > 1,
        !is_prime(n as int),
    ensures 
        result as int > 1,
        (n as int) % (result as int) == 0,
        forall|k: int| k > result as int && (n as int) % k == 0 ==> !is_prime(k),
        is_prime(result as int),
// </vc-spec>
// <vc-code>
{
    let n_int = n as int;
    let mut i = n - 1;

    lemma_non_prime_has_prime_factor_lt(n_int);

    while i >= 2
        invariant
            n_int == n as int,
            !is_prime(n_int),
            1 <= i < n,
            forall|k: int| (i as int) < k < n_int ==> !(is_prime(k) && n_int % k == 0),
        decreases i
    {
        if n % i == 0 {
            if exec_is_prime(i) {
                return i;
            }
        }
        i = i - 1;
    }

    unreached();
}
// </vc-code>


}

fn main() {}
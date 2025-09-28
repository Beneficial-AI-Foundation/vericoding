// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_triple(a: int, b: int, c: int, n: int, k: int) -> bool
    recommends k >= 1
{
    1 <= a <= n && 1 <= b <= n && 1 <= c <= n &&
    (a + b) % k == 0 && (b + c) % k == 0 && (c + a) % k == 0
}

spec fn count_valid_triples(n: int, k: int) -> int
    recommends n >= 1 && k >= 1
{
    if k % 2 == 1 {
        let cnt1 = n / k;
        cnt1 * cnt1 * cnt1
    } else {
        let cnt1 = n / k;
        let cnt2 = n / k + (if n % k >= k / 2 { 1int } else { 0int });
        cnt1 * cnt1 * cnt1 + cnt2 * cnt2 * cnt2
    }
}

spec fn valid_input(n: int, k: int) -> bool {
    n >= 1 && k >= 1
}

spec fn count_divisible_by_k(n: int, k: int) -> int
    recommends k >= 1
{
    if n <= 0 { 0int } else { n / k }
}

spec fn count_with_remainder_half_k(n: int, k: int) -> int
    recommends k >= 1
{
    if n <= 0 { 0int } else { n / k + (if n % k >= k / 2 { 1int } else { 0int }) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): [updated internal Verus API calls] */
proof fn lemma_count_valid_triples_is_nonnegative(n: int, k: int)
    requires
        valid_input(n, k),
    ensures
        count_valid_triples(n, k) >= 0,
{
    let cnt1 = n / k;
    assert(cnt1 >= 0) by {
        vstd::arithmetic::div_mul::lemma_div_is_pos(n, k);
    };
    assert(cnt1 * cnt1 * cnt1 >= 0);

    if k % 2 == 0 {
        assert(n % k >= 0) by {
            vstd::arithmetic::mod_ops::lemma_mod_range(n, k);
        };
        let cnt2 = n / k + (if n % k >= k / 2 { 1int } else { 0int });
        assert(cnt2 >= cnt1);
        assert(cnt2 >= 0);
        assert(cnt2 * cnt2 * cnt2 >= 0);
        assert(count_valid_triples(n, k) >= 0);
    } else {
        assert(count_valid_triples(n, k) >= 0);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
    requires 
        valid_input(n as int, k as int)
    ensures 
        result >= 0,
        result as int == count_valid_triples(n as int, k as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): [used i64 for calculations to avoid overflow and fixed ghost type issues] */
    let n_64 = n as i64;
    let k_64 = k as i64;
    let result_64: i64;

    if k % 2 == 1 {
        let cnt1 = n_64 / k_64;
        result_64 = cnt1 * cnt1 * cnt1;
    } else {
        let cnt1 = n_64 / k_64;
        let cnt2 = n_64 / k_64 + (if n % k >= k / 2 { 1 } else { 0 });
        result_64 = (cnt1 * cnt1 * cnt1) + (cnt2 * cnt2 * cnt2);
    }

    proof {
        let n_int = n as int;
        let k_int = k as int;
        assert(result_64 == count_valid_triples(n_int, k_int));
        lemma_count_valid_triples_is_nonnegative(n_int, k_int);
    }

    result_64 as i8
}
// </vc-code>


}

fn main() {}
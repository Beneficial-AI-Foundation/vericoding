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
/* helper modified by LLM (iteration 4): lemma connecting count_valid_triples spec to its expression */
proof fn lemma_count_formula(n: int, k: int)
    requires
        valid_input(n, k),
    ensures
        count_valid_triples(n, k) ==
            if k % 2 == 1 {
                let cnt1 = n / k;
                cnt1 * cnt1 * cnt1
            } else {
                let cnt1 = n / k;
                let cnt2 = n / k + (if n % k >= k / 2 { 1int } else { 0int });
                cnt1 * cnt1 * cnt1 + cnt2 * cnt2 * cnt2
            },
{
    if k % 2 == 1 {
        let cnt1 = n / k;
        assert(count_valid_triples(n, k) == cnt1 * cnt1 * cnt1);
    } else {
        let cnt1 = n / k;
        let cnt2 = n / k + (if n % k >= k / 2 { 1int } else { 0int });
        assert(count_valid_triples(n, k) == cnt1 * cnt1 * cnt1 + cnt2 * cnt2 * cnt2);
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
    /* code modified by LLM (iteration 4): compute result in concrete integers and prove equality with spec */
    let n_i32: i32 = n as i32;
    let k_i32: i32 = k as i32;
    let total_i32: i32 = if k_i32 % 2 == 1 {
        let cnt1 = n_i32 / k_i32;
        cnt1 * cnt1 * cnt1
    } else {
        let cnt1 = n_i32 / k_i32;
        let cnt2 = n_i32 / k_i32 + (if n_i32 % k_i32 >= k_i32 / 2 { 1i32 } else { 0i32 });
        cnt1 * cnt1 * cnt1 + cnt2 * cnt2 * cnt2
    };
    let result: i8 = total_i32 as i8;
    proof {
        let n_int: int = n as int;
        let k_int: int = k as int;
        lemma_count_formula(n_int, k_int);
        if k_int % 2 == 1 {
            let cnt1_spec = n_int / k_int;
            let cnt1_r: int = (n_i32 / k_i32) as int;
            assert(cnt1_r == cnt1_spec);
            assert(result as int == cnt1_spec * cnt1_spec * cnt1_spec);
            assert(result as int == count_valid_triples(n_int, k_int));
        } else {
            let cnt1_spec = n_int / k_int;
            let cnt2_spec = n_int / k_int + (if n_int % k_int >= k_int / 2 { 1int } else { 0int });
            let cnt1_r: int = (n_i32 / k_i32) as int;
            let cnt2_r: int = (n_i32 / k_i32 + (if n_i32 % k_i32 >= k_i32 / 2 { 1i32 } else { 0i32 })) as int;
            assert(cnt1_r == cnt1_spec);
            assert(cnt2_r == cnt2_spec);
            assert(result as int == cnt1_spec * cnt1_spec * cnt1_spec + cnt2_spec * cnt2_spec * cnt2_spec);
            assert(result as int == count_valid_triples(n_int, k_int));
        }
    }
    result
}
// </vc-code>


}

fn main() {}
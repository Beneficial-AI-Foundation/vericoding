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
/* code modified by LLM (iteration 5): use u64 for intermediate calculations to avoid overflow */
{
    let n_u64 = n as u64;
    let k_u64 = k as u64;

    let result_u64: u64 = if k_u64 % 2 == 1 {
        let cnt1 = n_u64 / k_u64;
        let square = cnt1 * cnt1;
        let cube = square * cnt1;
        cube
    } else {
        let cnt1 = n_u64 / k_u64;
        let rem = n_u64 % k_u64;
        let half_k = k_u64 / 2;
        let cnt2 = if rem >= half_k { cnt1 + 1 } else { cnt1 };
        let square1 = cnt1 * cnt1;
        let cube1 = square1 * cnt1;
        let square2 = cnt2 * cnt2;
        let cube2 = square2 * cnt2;
        cube1 + cube2
    };

    assert(result_u64 <= 127);

    let result_i8 = result_u64 as i8;

    proof {
        let n_int = n as int;
        let k_int = k as int;
        let spec_result = count_valid_triples(n_int, k_int);
        if k_int % 2 == 1 {
            let cnt1_spec = count_divisible_by_k(n_int, k_int);
            let cnt1_exec = n_u64 / k_u64;
            assert(cnt1_exec as int == cnt1_spec);
            let cube_exec = cnt1_exec * cnt1_exec * cnt1_exec;
            assert(cube_exec as int == cnt1_spec * cnt1_spec * cnt1_spec);
            assert(result_u64 as int == spec_result);
        } else {
            let cnt1_spec = count_divisible_by_k(n_int, k_int);
            let cnt1_exec = n_u64 / k_u64;
            assert(cnt1_exec as int == cnt1_spec);
            let rem_spec = n_int % k_int;
            let rem_exec = n_u64 % k_u64;
            assert(rem_exec as int == rem_spec);
            let half_k_spec = k_int / 2;
            let half_k_exec = k_u64 / 2;
            assert(half_k_exec as int == half_k_spec);
            let cnt2_spec = count_with_remainder_half_k(n_int, k_int);
            let cnt2_exec = if rem_exec >= half_k_exec { cnt1_exec + 1 } else { cnt1_exec };
            assert(cnt2_exec as int == cnt2_spec);
            let cube_exec = cnt1_exec * cnt1_exec * cnt1_exec + cnt2_exec * cnt2_exec * cnt2_exec;
            assert(cube_exec as int == cnt1_spec * cnt1_spec * cnt1_spec + cnt2_spec * cnt2_spec * cnt2_spec);
            assert(result_u64 as int == spec_result);
        }
    }

    result_i8
}
// </vc-code>


}

fn main() {}
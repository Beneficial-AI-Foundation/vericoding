// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, k: int) -> bool
{
    n >= 1 && k >= 0 && k <= n
}

spec fn valid_output(result: Seq<int>, n: int, k: int) -> bool
{
    result.len() == 2 && 
    result[0] >= 0 && 
    result[1] >= 0 && 
    result[0] <= result[1] &&
    result[0] <= n - k &&
    result[1] <= n - k
}

spec fn min_good_apartments(n: int, k: int) -> int
{
    if k == 0 || k == n { 0 } else { 1 }
}

spec fn max_good_apartments(n: int, k: int) -> int
{
    if k == 0 || k == n { 0 }
    else if n - k < k * 2 { n - k }
    else { k * 2 }
}
// </vc-preamble>

// <vc-helpers>
fn compute_min(n: i8, k: i8) -> (min_val: i8)
    requires
        valid_input(n as int, k as int),
    ensures
        min_val as int == min_good_apartments(n as int, k as int),
{
    if k == 0 || k == n {
        0
    } else {
        1
    }
}

/* helper modified by LLM (iteration 3): fixed compilation errors by using i8 arithmetic */
fn compute_max(n: i8, k: i8) -> (max_val: i8)
    requires
        valid_input(n as int, k as int),
    ensures
        max_val as int == max_good_apartments(n as int, k as int),
{
    if k == 0 || k == n {
        0
    } else {
        let condition = if k > 42 { true } else { n < k * 3 };
        if condition {
            n - k
        } else {
            k * 2
        }
    }
}

/* helper modified by LLM (iteration 3): completed proof */
proof fn min_le_max_lemma(n: int, k: int)
    requires
        valid_input(n, k),
    ensures
        min_good_apartments(n, k) <= max_good_apartments(n, k),
{
    if k == 0 || k == n {
        // min is 0, max is 0. 0 <= 0 holds.
    } else { // k > 0 && k < n
        assert(min_good_apartments(n, k) == 1);
        let max_val = max_good_apartments(n, k);
        if n - k < k * 2 {
            assert(max_val == n - k);
            assert(k < n);
            assert(n - k >= 1);
        } else {
            assert(max_val == k * 2);
            assert(k > 0);
            assert(k >= 1);
            assert(k * 2 >= 2);
        }
        assert(max_val >= 1);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: Vec<i8>)
    requires valid_input(n as int, k as int)
    ensures 
        result.len() == 2 &&
        valid_output(result@.map(|i: int, x: i8| x as int), n as int, k as int) &&
        result[0] as int == min_good_apartments(n as int, k as int) &&
        result[1] as int == max_good_apartments(n as int, k as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): no change, relies on fixed helpers */
    let min_val = compute_min(n, k);
    let max_val = compute_max(n, k);

    let mut result = Vec::new();
    result.push(min_val);
    result.push(max_val);
    
    proof {
        min_le_max_lemma(n as int, k as int);
    }

    result
}
// </vc-code>


}

fn main() {}
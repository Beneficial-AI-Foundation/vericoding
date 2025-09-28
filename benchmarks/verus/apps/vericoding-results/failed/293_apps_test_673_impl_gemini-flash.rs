// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int) -> bool {
    n >= 1 && k > 0
}

spec fn is_correct_result(n: int, k: int, result: int) -> bool 
    recommends k > 0
{
    result > n && result % k == 0 && forall|x: int| n < x < result ==> #[trigger] (x % k) != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes. */
spec fn next_multiple_of_k(n: int, k: int) -> int {
    if n % k == 0 {
        n
    } else {
        n - (n % k) + k
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
    requires valid_input(n as int, k as int)
    ensures is_correct_result(n as int, k as int, result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error by making `n_int` and `k_int` ghost variables, and then converting them back to i8 for the final `result`. */
{
    let n_int: Ghost<int> = Ghost(n as int);
    let k_int: Ghost<int> = Ghost(k as int);

    let next_n = if n_int@ % k_int@ == 0 { n_int@ + k_int@ } else { n_int@ - (n_int@ % k_int@) + k_int@ };
    let result_int = next_n;

    assert(result_int > n_int@);
    assert(result_int % k_int@ == 0);

    let result = result_int as i8;
    result
}
// </vc-code>


}

fn main() {}
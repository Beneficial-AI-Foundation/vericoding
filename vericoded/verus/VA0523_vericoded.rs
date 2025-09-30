// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, k: int) -> bool {
    n >= 0 && k >= 1
}

spec fn min_value(n: int, k: int) -> int
    recommends valid_input(n, k)
{
    let remainder = n % k;
    let complement = k - remainder;
    if remainder <= complement { remainder } else { complement }
}

spec fn is_correct_result(n: int, k: int, result: int) -> bool
    recommends valid_input(n, k)
{
    result == min_value(n, k) &&
    result >= 0 &&
    result < k
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): identity on int for proofs */
spec fn id_int(a: int) -> int { a }
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
    requires valid_input(n as int, k as int)
    ensures is_correct_result(n as int, k as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): compute using i8 and prove correspondence to spec using a proof block */
    let rem_i8: i8 = n % k;
    let complement_i8: i8 = k - rem_i8;
    let result: i8 = if rem_i8 <= complement_i8 { rem_i8 } else { complement_i8 };
    proof {
        let n_i: int = n as int;
        let k_i: int = k as int;
        let remainder = n_i % k_i;
        let complement = k_i - remainder;
        reveal(min_value);
        assert(remainder == (rem_i8 as int));
        assert(complement == (complement_i8 as int));
        assert(min_value(n_i, k_i) == if remainder <= complement { remainder } else { complement });
        assert((result as int) == min_value(n_i, k_i));
        assert((result as int) >= 0 && (result as int) < k_i);
    }
    result
}
// </vc-code>


}

fn main() {}
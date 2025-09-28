// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    n >= 1
}

spec fn sum_from_one_to_n(n: int) -> int
    recommends n >= 1
{
    n * (n + 1) / 2
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma stating closed-form equals its definition */
proof fn lemma_sum_closed_form(n: int)
    requires
        n >= 1,
    ensures
        sum_from_one_to_n(n) == n * (n + 1) / 2,
{
}

// </vc-helpers>

// <vc-spec>
fn sum_to_n(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == sum_from_one_to_n(n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute using wider i16 arithmetic to avoid using ghost ints in exec code */
    let n16: i16 = n as i16;
    let total16: i16 = n16 * (n16 + 1) / 2;
    let result: i8 = total16 as i8;
    result
}
// </vc-code>


}

fn main() {}
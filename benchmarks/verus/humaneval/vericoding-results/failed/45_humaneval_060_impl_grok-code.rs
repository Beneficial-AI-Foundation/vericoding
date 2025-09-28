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

// </vc-helpers>

// <vc-spec>
fn sum_to_n(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == sum_from_one_to_n(n as int)
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): Implemented summation loop using i16 to prevent overflow during intermediate calculations, added assertions for preconditions and bounds */
    assert(n as int >= 1);
    assert(n as int * (n as int + 1) / 2 <= i8::MAX as int);
    let n_int = n as i16;
    let mut sum = 0i16;
    let mut i = 1i16;
    while i <= n_int
        invariant
            n as int >= 1,
            sum as int == sum_from_one_to_n(i as int - 1),
            i >= 1,
            i <= n_int + 1,
            n as int * (n as int + 1) / 2 <= i8::MAX as int,
        decreases (n_int as int - i as int)
    {
        sum = sum + i;
        i = i + 1;
    }
    sum as i8
}
// </vc-code>


}

fn main() {}
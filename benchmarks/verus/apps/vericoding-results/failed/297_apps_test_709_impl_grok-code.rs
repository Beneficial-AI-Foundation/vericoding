// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_ones_in_binary(n: int) -> int
    recommends n >= 1
    decreases n
    when n >= 1
{
    if n == 1 {
        1
    } else if n % 2 == 1 {
        1 + count_ones_in_binary(n / 2)
    } else {
        count_ones_in_binary(n / 2)
    }
}

spec fn valid_input(x: int) -> bool {
    x >= 1
}

spec fn valid_output(x: int, result: int) -> bool {
    valid_input(x) && result == count_ones_in_binary(x)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added count_ones spec function that works for all integers */
spec fn count_ones (n: int) -> int
    decreases n when n > 0
{
    if n <= 0 {
        0
    } else if n == 1 {
        1
    } else if n % 2 == 1 {
        1 + count_ones (n / 2)
    } else {
        count_ones (n / 2)
    }
}
// </vc-helpers>

// <vc-spec>
fn min_bacteria(x: i8) -> (result: i8)
    requires valid_input(x as int)
    ensures valid_output(x as int, result as int)
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): used count_ones spec for invariant, used i8 for count to avoid cast warning */
    let mut count: i8 = 0;
    let mut n: u8 = x as u8;
    while n > 0
        invariant
            count_ones(x as int) == (count as int) + count_ones(n as int),
        decreases n as nat
    {
        if (n & 1) == 1 {
            count += 1;
        }
        n >>= 1;
    }
    count
}
// </vc-code>


}

fn main() {}
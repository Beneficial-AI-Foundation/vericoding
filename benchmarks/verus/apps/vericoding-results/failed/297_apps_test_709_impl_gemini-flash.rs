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

// </vc-helpers>

// <vc-spec>
fn min_bacteria(x: i8) -> (result: i8)
    requires valid_input(x as int)
    ensures valid_output(x as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [converted `n` and `count` to `i8` types and added ghost variables for verification] */
    let mut n: i8 = x;
    let mut count: i8 = 0;
    let ghost mut ghost_n: int = x as int;
    let ghost mut ghost_count: int = 0;

    while n > 0
        invariant
            n >= 0,
            count >= 0,
            ghost_n >= 0,
            ghost_count >= 0,
            (x as int) >= 1,
            ghost_n == n as int,
            ghost_count == count as int,
            ghost_count == (count_ones_in_binary(x as int) - count_ones_in_binary(ghost_n)) || (ghost_n == x as int && ghost_count == 0),
        decreases n
    {
        if n % 2 == 1 {
            count = count + 1;
            ghost_count = ghost_count + 1;
        }
        n = n / 2;
        ghost_n = ghost_n / 2;
    }
    count
}
// </vc-code>


}

fn main() {}
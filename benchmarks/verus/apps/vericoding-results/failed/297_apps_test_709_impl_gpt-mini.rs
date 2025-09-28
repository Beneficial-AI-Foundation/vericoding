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
proof fn lemma_trivial(n: int)
    requires n >= 1
    ensures n >= 1
{
}

// </vc-helpers>

// <vc-spec>
fn min_bacteria(x: i8) -> (result: i8)
    requires valid_input(x as int)
    ensures valid_output(x as int, result as int)
// </vc-spec>
// <vc-code>
{
    let orig: int = x as int;
    let mut n: int = orig;
    let mut acc: int = 0;

    while n > 1
        invariant
            1 <= n,
            acc >= 0,
            acc + count_ones_in_binary(n) == count_ones_in_binary(orig),
        decreases n
    {
        if n % 2 == 1 {
            acc = acc + 1;
            n = n / 2;
        } else {
            n = n / 2;
        }
    }

    // now n == 1
    let res_int: int = acc + 1;
    let result: i8 = res_int as i8;
    result
}

// </vc-code>


}

fn main() {}
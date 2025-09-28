// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn lucas(n: int) -> int
    recommends n >= 0
    decreases n
{
    if n <= 0 {
        2
    } else if n == 1 {
        1
    } else {
        lucas(n - 1) + lucas(n - 2)
    }
}

spec fn valid_input(n: int) -> bool {
    1 <= n <= 86
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == lucas(n as int)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        2 as i8
    } else if n == 1 {
        1 as i8
    } else {
        let n_int = n as int;
        let mut a: int = 2;
        let mut b: int = 1;
        let mut i: int = 2;
        while i <= n_int
            invariant
                a == lucas(i - 2),
                b == lucas(i - 1),
                2 <= i <= n_int + 1,
            decreases n_int - i
        {
            let next = a + b;
            a = b;
            b = next;
            i += 1;
        }
        b as i8
    }
}
// </vc-code>


}

fn main() {}
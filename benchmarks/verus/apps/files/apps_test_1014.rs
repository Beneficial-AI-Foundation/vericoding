// <vc-preamble>
use vstd::prelude::*;
use vstd::string::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int) -> bool {
    n >= 2
}

spec fn is_win_for_white(n: int) -> bool {
    n % 2 == 0
}

spec fn is_win_for_black(n: int) -> bool {
    n % 2 == 1
}

spec fn optimal_white_move(n: int) -> (int, int)
    recommends valid_input(n) && is_win_for_white(n)
{
    (1, 2)
}

spec fn valid_result(n: int, result: String) -> bool
    recommends valid_input(n)
{
    if is_win_for_black(n) {
        result@ == "black\n"@
    } else {
        result@ == "white\n1 2\n"@
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int) -> (result: String)
    requires valid_input(n)
    ensures valid_result(n, result)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}
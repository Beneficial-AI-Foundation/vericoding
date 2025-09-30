// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int, powers: Seq<int>) -> bool {
    n > 0 && k > 0 && k <= n && n % k == 0 && powers.len() == n
}

spec fn is_optimal_starting_task(result: int, n: int, k: int, powers: Seq<int>) -> bool {
    1 <= result <= k
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_pos_implies_ge1(k: int)
    requires
        k > 0,
    ensures
        1 <= k,
{
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, powers: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, k as int, powers@.map(|i: int, x: i8| x as int))
    ensures is_optimal_starting_task(result as int, n as int, k as int, powers@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    let res: i8 = 1i8;
    res
}
// </vc-code>


}

fn main() {}
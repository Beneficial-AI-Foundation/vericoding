// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int, pairs: Seq<(int, int)>) -> bool {
    n >= 2 && 
    m >= 0 && 
    pairs.len() == m &&
    (forall|i: int| 0 <= i < pairs.len() ==> #[trigger] pairs[i].0 >= 1 && #[trigger] pairs[i].0 <= n && #[trigger] pairs[i].1 >= 1 && #[trigger] pairs[i].1 <= n) &&
    (forall|i: int| 0 <= i < pairs.len() ==> #[trigger] pairs[i].0 != #[trigger] pairs[i].1)
}

spec fn compute_final_l(pairs: Seq<(int, int)>) -> int
    decreases pairs.len()
{
    if pairs.len() == 0 { 1 }
    else {
        let x = pairs[pairs.len() - 1].0;
        let y = pairs[pairs.len() - 1].1;
        let min_val = if x < y { x } else { y };
        let rest_l = compute_final_l(pairs.subrange(0, pairs.len() - 1));
        if rest_l > min_val { rest_l } else { min_val }
    }
}

spec fn compute_final_r(n: int, pairs: Seq<(int, int)>) -> int
    decreases pairs.len()
{
    if pairs.len() == 0 { n }
    else {
        let x = pairs[pairs.len() - 1].0;
        let y = pairs[pairs.len() - 1].1;
        let max_val = if x > y { x } else { y };
        let rest_r = compute_final_r(n, pairs.subrange(0, pairs.len() - 1));
        if rest_r < max_val { rest_r } else { max_val }
    }
}

spec fn max(a: int, b: int) -> int {
    if a > b { a } else { b }
}

spec fn valid_result(n: int, pairs: Seq<(int, int)>, result: int) -> bool {
    result >= 0 &&
    result <= n - 1 &&
    result == max(compute_final_r(n, pairs) - compute_final_l(pairs), 0)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, m: int, pairs: Seq<(int, int)>) -> (result: int)
    requires valid_input(n, m, pairs)
    ensures valid_result(n, pairs, result)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}
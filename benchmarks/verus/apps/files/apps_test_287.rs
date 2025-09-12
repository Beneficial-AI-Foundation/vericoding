// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, k: int) -> bool
{
    n >= 1 && k >= 0 && k <= n
}

spec fn valid_output(result: Seq<int>, n: int, k: int) -> bool
{
    result.len() == 2 && 
    result[0] >= 0 && 
    result[1] >= 0 && 
    result[0] <= result[1] &&
    result[0] <= n - k &&
    result[1] <= n - k
}

spec fn min_good_apartments(n: int, k: int) -> int
{
    if k == 0 || k == n { 0 } else { 1 }
}

spec fn max_good_apartments(n: int, k: int) -> int
{
    if k == 0 || k == n { 0 }
    else if n - k < k * 2 { n - k }
    else { k * 2 }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, k: int) -> (result: Vec<int>)
    requires valid_input(n, k)
    ensures 
        result.len() == 2 &&
        valid_output(result@, n, k) &&
        result[0] == min_good_apartments(n, k) &&
        result[1] == max_good_apartments(n, k)
// </vc-spec>
// <vc-code>
{
    assume(false);
    Vec::new()
}
// </vc-code>


}

fn main() {}
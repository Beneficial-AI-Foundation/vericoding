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
fn solve(n: i8, k: i8) -> (result: Vec<i8>)
    requires valid_input(n as int, k as int)
    ensures 
        result.len() == 2 &&
        valid_output(result@.map(|i: int, x: i8| x as int), n as int, k as int) &&
        result[0] as int == min_good_apartments(n as int, k as int) &&
        result[1] as int == max_good_apartments(n as int, k as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    Vec::new()
}
// </vc-code>


}

fn main() {}
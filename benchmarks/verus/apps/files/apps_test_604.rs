// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(arr: Seq<int>) -> bool {
    true
}

spec fn distinct_non_zero_count(arr: Seq<int>) -> int {
    Set::<int>::new(|x: int| arr.contains(x) && x != 0).len() as int
}
// </vc-helpers>

// <vc-spec>
fn solve(arr: Seq<int>) -> (result: int)
    requires 
        valid_input(arr)
    ensures 
        result >= 0,
        result <= arr.len(),
        result == distinct_non_zero_count(arr)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}
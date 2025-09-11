// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_subrange_at(main: Seq<i32>, sub: Seq<i32>, i: int) -> (result: bool) {
    sub =~= main.subrange(i, i+sub.len())
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_sub_array(main: &Vec<i32>, sub: &Vec<i32>) -> (result: bool)

    ensures
        result == (exists|k: int|
            0 <= k <= (main.len() - sub.len()) && is_subrange_at(main@, sub@, k)),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}
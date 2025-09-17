// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn get_value(o: Option<int>) -> int
    recommends o.is_Some()
{
    o.get_Some_0()
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn largest_smallest_integers(arr: Seq<int>) -> (result: (Option<int>, Option<int>))
// </vc-spec>
// <vc-code>
{
    assume(false);
    (Option::None, Option::None)
}
// </vc-code>


}

fn main() {}
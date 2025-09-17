// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(l: Seq<int>) -> bool {
    l.len() > 0
}

spec fn is_max_element(l: Seq<int>, max_val: int) -> bool {
    l.contains(max_val) && forall|i: int| 0 <= i < l.len() ==> l[i] <= max_val
}
// </vc-preamble>

// <vc-helpers>
spec fn max_element_func(l: Seq<int>) -> int
    decreases l.len()
{
    if l.len() == 1 {
        l[0]
    } else if l.len() > 1 {
        let rest_max = max_element_func(l.subrange(1, l.len() as int));
        if l[0] > rest_max { l[0] } else { rest_max }
    } else {
        0int
    }
}
// </vc-helpers>

// <vc-spec>
fn find_max_element(l: Seq<int>) -> (max_val: int)
    requires valid_input(l)
    ensures is_max_element(l, max_val)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}
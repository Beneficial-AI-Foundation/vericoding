// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(l: Seq<int>) -> bool {
    l.len() > 0
}

spec fn is_max_element(l: Seq<int>, max_val: int) -> bool {
    l.contains(max_val) && forall|i: int| 0 <= i < l.len() ==> l[i] <= max_val
}

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

// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed helper, not needed */
// </vc-helpers>

// <vc-spec>
fn find_max_element(l: Vec<i8>) -> (max_val: i8)
    requires valid_input(l@.map(|i, x| x as int))
    ensures is_max_element(l@.map(|i, x| x as int), max_val as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): corrected loop invariant range for is_max_element to include the initial max_val */
{
    let mut max_val = l[0];
    let mut i = 1;

    while i < l.len()
        invariant
            0 <= i && i <= l.len(),
            is_max_element(l@.subrange(0, i as int).map(|k, x| x as int), max_val as int),
            l.len() > 0
        decreases l.len() - i
    {
        if l[i] > max_val {
            max_val = l[i];
        }
        i = i + 1;
    }
    proof {
        // At the end of the loop, i == l.len(), so the invariant implies the postcondition
        assert(is_max_element(l@.subrange(0, l.len() as int).map(|k, x| x as int), max_val as int));
    }
    max_val
}
// </vc-code>


}

fn main() {}
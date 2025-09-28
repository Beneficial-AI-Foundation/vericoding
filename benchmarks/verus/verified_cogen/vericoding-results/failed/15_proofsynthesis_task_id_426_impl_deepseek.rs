// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix FnSpec type compatibility for filter */
fn is_odd(x: u32) -> bool {
    x % 2 != 0
}

spec fn spec_is_odd(x: u32) -> bool {
    x % 2 != 0
}

proof fn spec_is_odd_fnspec() -> FnSpec<u32, bool> {
    ensures |x: u32| result.requires(x) && result.ensures(x, spec_is_odd(x));
    FnSpec(|x: u32| spec_is_odd(x))
}
// </vc-helpers>

// <vc-spec>
fn filter_odd_numbers(arr: &Vec<u32>) -> (odd_list: Vec<u32>)

    ensures
        odd_list@ == arr@.filter(|x: u32| x % 2 != 0),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): use FnSpec wrapper for filter function */
{
    let mut odd_list = Vec::new();
    let mut i = 0;
    while i < arr.len()
        invariant
            odd_list@ == arr@.subrange(0, i as int).filter(spec_is_odd_fnspec()),
        decreases arr.len() - i
    {
        if arr[i] % 2 != 0 {
            odd_list.push(arr[i]);
        }
        i += 1;
    }
    proof {
        let fnspec = spec_is_odd_fnspec();
        assert(odd_list@ == arr@.filter(fnspec));
    }
    odd_list
}
// </vc-code>

}
fn main() {}
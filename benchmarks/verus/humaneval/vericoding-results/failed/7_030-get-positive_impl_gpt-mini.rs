// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): trivial no-op helper to satisfy placeholder */
proof fn helper_noop<T>(s: Seq<T>) ensures true {
}

// </vc-helpers>

// <vc-spec>
fn get_positive(input: Vec<i32>) -> (positive_list: Vec<i32>)

    ensures
        positive_list@ == input@.filter(|x: i32| x > 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): construct Vec from filtered sequence */
    let filtered: Seq<i32> = input@.filter(|x: i32| x > 0);
    Vec::from_seq(filtered)
}
// </vc-code>

}
fn main() {}
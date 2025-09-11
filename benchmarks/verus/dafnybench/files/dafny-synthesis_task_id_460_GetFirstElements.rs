// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn get_first_elements(lst: Vec<Vec<i32>>) -> (result: Vec<i32>)
    requires forall|i: int| 0 <= i < lst.len() ==> lst[i].len() > 0,
    ensures 
        result.len() == lst.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == lst[i][0],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}
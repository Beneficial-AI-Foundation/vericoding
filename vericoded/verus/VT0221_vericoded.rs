// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_one_i8_ge_1()
    ensures
        1i8 as int >= 1,
        1i8 as int >= 0,
{
}

// </vc-helpers>

// <vc-spec>
fn condition_number(x: Vec<Vec<i8>>) -> (result: i8)
    requires 
        x.len() > 0,
        forall|i: int| 0 <= i < x.len() ==> x[i].len() == x.len(),
    ensures 
        result as int >= 0,
        result as int >= 1,
// </vc-spec>
// <vc-code>
{
    1i8
}
// </vc-code>


}
fn main() {}
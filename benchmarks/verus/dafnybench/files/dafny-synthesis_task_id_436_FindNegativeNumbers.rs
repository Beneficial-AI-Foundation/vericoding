// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_negative(n: int) -> bool {
    n < 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_negative_numbers(arr: &[i8]) -> (negative_list: Vec<i8>)
    ensures

        forall|i: int| 0 <= i < negative_list@.len() ==> 
            is_negative(negative_list@[i] as int) && exists|j: int| 0 <= j < arr@.len() && arr@[j] == negative_list@[i],

        forall|i: int| 0 <= i < arr@.len() && is_negative(arr@[i] as int) ==> 
            exists|j: int| 0 <= j < negative_list@.len() && negative_list@[j] == arr@[i],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}
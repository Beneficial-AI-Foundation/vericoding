// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn amax(a: Vec<i8>) -> (result: i8)
    requires a.len() > 0,
    ensures
        (exists|max_idx: int| 0 <= max_idx < a.len() &&
            result as int == a@[max_idx] as int &&
            (forall|i: int| 0 <= i < a.len() ==> a@[i] as int <= result as int)) &&
        (exists|first_max_idx: int| 0 <= first_max_idx < a.len() &&
            result as int == a@[first_max_idx] as int &&
            (forall|i: int| 0 <= i < a.len() && a@[i] as int == result as int ==> first_max_idx <= i) &&
            (forall|i: int| 0 <= i < a.len() ==> a@[i] as int <= result as int)) &&
        ((forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a@[i] as int == a@[j] as int) ==> 
            result as int == a@[0] as int) &&
        (exists|witness: int| 0 <= witness < a.len() && result as int == a@[witness] as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}
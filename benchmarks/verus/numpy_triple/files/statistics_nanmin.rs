// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn all_nan(a: Seq<int>) -> bool 
    decreases a.len()
{
    false  /* integers can't be NaN */
}

spec fn has_non_nan(a: Seq<int>) -> bool 
    decreases a.len()
{
    a.len() > 0  /* all integers are non-NaN */
}

spec fn is_min_of_all(result: int, a: Seq<int>) -> bool {
    exists|witness: int| 0 <= witness < a.len() &&
        result == a[witness] &&
        forall|j: int| 0 <= j < a.len() ==> result <= a[j]
}

fn nanmin(a: Vec<i8>) -> (result: i8)
    requires a.len() > 0,
    ensures is_min_of_all(result as int, a@.map(|i, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}
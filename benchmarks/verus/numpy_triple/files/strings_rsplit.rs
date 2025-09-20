// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn rsplit(a: Vec<String>, sep: String, maxsplit: u8) -> (result: Vec<Vec<String>>)
    requires 
        sep@.len() > 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() > 0,
        maxsplit as int == 0 ==> forall|i: int| 0 <= i < result.len() ==> 
            result[i].len() == 1 && result[i][0]@ == a[i]@,
        forall|i: int| 0 <= i < result.len() ==> result[i].len() <= maxsplit as int + 1,
        forall|i: int| 0 <= i < result.len() ==> 
            (a[i]@.len() == 0 ==> result[i].len() == 1 && result[i][0]@.len() == 0),
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
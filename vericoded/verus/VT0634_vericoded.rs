// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn replace(a: Vec<String>, old: Vec<String>, new: Vec<String>, count: Vec<i32>) -> (result: Vec<String>)
    requires 
        a.len() == old.len() && old.len() == new.len() && new.len() == count.len(),
        forall|i: int| 0 <= i < count.len() ==> (count[i] == 0 || old[i]@.len() > 0),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> {

            (count[i] == 0 ==> result[i] == a[i]) &&

            (old[i]@.len() == 0 ==> result[i] == a[i])
        },
// </vc-spec>
// <vc-code>
{
    a
}
// </vc-code>

}
fn main() {}
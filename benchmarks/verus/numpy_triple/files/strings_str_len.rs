use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn str_len(a: Vec<String>) -> (result: Vec<nat>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            &&& result[i] == a[i]@.len()
            &&& result[i] >= 0
            &&& (a[i]@.len() == 0 <==> a[i]@ == Seq::<char>::empty())
        }
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}
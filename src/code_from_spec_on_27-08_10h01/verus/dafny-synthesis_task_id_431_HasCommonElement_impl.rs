use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn has_common_element(a: &[i32], b: &[i32]) -> (result: bool)
    ensures 
        result ==> (exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && a[i] == b[j]) &&
        (!result ==> (forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() ==> a[i] != b[j]))
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    for i in 0..a.len()
        invariant
            forall|ii: int, j: int| 0 <= ii < i && 0 <= j < b.len() ==> a@[ii] != b@[j]
    {
        for j in 0..b.len()
            invariant
                forall|ii: int, jj: int| 0 <= ii < i && 0 <= jj < b.len() ==> a@[ii] != b@[jj],
                forall|jj: int| 0 <= jj < j ==> a@[i as int] != b@[jj]
        {
            if a[i] == b[j] {
                proof {
                    assert(0 <= i < a.len() && 0 <= j < b.len() && a[i as int] == b[j as int]);
                }
                return true;
            }
        }
    }
    false
}
// </vc-code>

fn main() {}

}
use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn has_common_element(a: &[i32], b: &[i32]) -> (result: bool)
    ensures 
        result ==> (exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && a[i] == b[j]) &&
        (!result ==> (forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() ==> a[i] != b[j]))
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|ii: int, jj: int| 0 <= ii < i && 0 <= jj < b.len() ==> a[ii] != b[jj],
        decreases a.len() - i,
    {
        let mut j: usize = 0;
        while j < b.len()
            invariant
                0 <= i < a.len(),
                0 <= j <= b.len(),
                forall|ii: int, jj: int| 0 <= ii < i && 0 <= jj < b.len() ==> a[ii] != b[jj],
                forall|jj: int| 0 <= jj < j ==> a[i as int] != b[jj],
            decreases b.len() - j,
        {
            if a[i] == b[j] {
                assert(0 <= i < a.len() && 0 <= j < b.len() && a[i as int] == b[j as int]);
                return true;
            }
            j = j + 1;
        }
        assert(forall|jj: int| 0 <= jj < b.len() ==> a[i as int] != b[jj]);
        i = i + 1;
    }
    assert(forall|ii: int, jj: int| 0 <= ii < a.len() && 0 <= jj < b.len() ==> a[ii] != b[jj]);
    false
}
// </vc-code>

fn main() {}

}
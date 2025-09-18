// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn has_common_element(a: &Vec<i32>, b: &Vec<i32>) -> (result: bool)
    requires 
        a.len() > 0,
        b.len() > 0,
    ensures
        result == (exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && a[i] == b[j]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): added decreases clause to loops */
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|ii: int, jj: int| 0 <= ii < i as int && 0 <= jj < b.len() ==> a[ii] != b[jj],
        decreases a.len() - i,
    {
        let mut j: usize = 0;
        while j < b.len()
            invariant
                0 <= i < a.len(),
                0 <= j <= b.len(),
                forall|jj: int| 0 <= jj < j as int ==> a[i as int] != b[jj],
                forall|ii: int, jj: int| 0 <= ii < i as int && 0 <= jj < b.len() ==> a[ii] != b[jj],
            decreases b.len() - j,
        {
            if a[i] == b[j] {
                return true;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

}
fn main() {}
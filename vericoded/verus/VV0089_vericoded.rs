// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec for existence using int indices */
spec fn exists_common_spec(a: &Vec<i32>, b: &Vec<i32>) -> bool {
    exists|i: int, j: int| 0 <= i && i < a.len() && 0 <= j && j < b.len() && a[i] == b[j]
}

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
/* code modified by LLM (iteration 5): nested loops searching for common element with int-spec indexing */
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i as int <= a.len(),
            forall|ii: int, jj: int| 0 <= ii && ii < i as int && 0 <= jj && jj < b.len() ==> a[ii] != b[jj],
        decreases a.len() - i
    {
        let mut j: usize = 0;
        while j < b.len()
            invariant
                j as int <= b.len(),
                i < a.len(),
                forall|jj0: int| 0 <= jj0 && jj0 < j as int ==> a[i as int] != b[jj0],
            decreases b.len() - j
        {
            if a[i] == b[j] {
                proof {
                    let ii: int = i as int;
                    let jj: int = j as int;
                    assert(0 <= ii && ii < a.len());
                    assert(0 <= jj && jj < b.len());
                    assert(a[ii] == b[jj]);
                    assert(exists|iii: int, jjj: int| iii == ii && jjj == jj && a[iii] == b[jjj]);
                }
                return true;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    proof {
        assert(forall|ii: int, jj: int| 0 <= ii && ii < a.len() && 0 <= jj && jj < b.len() ==> a[ii] != b[jj]);
        assert(!exists|ii: int, jj: int| 0 <= ii && ii < a.len() && 0 <= jj && jj < b.len() && a[ii] == b[jj]);
    }
    false
}
// </vc-code>

}
fn main() {}
// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Fixed vec_new_filled by using Vec::new and adding an invariant. */
fn vec_new_filled(len: usize, val: i8) -> (v: Vec<i8>)
    ensures
        v.len() == len,
        forall|i: int| 0 <= i < len as int ==> v[i] == val,
{
    let mut v = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            v.len() == i,
            forall|j: int| 0 <= j < i as int ==> v[j] == val,
        decreases len - i
    {
        v.push(val);
        i = i + 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn broadcast_arrays(a: Vec<i8>, b: Vec<i8>) -> (result: (Vec<i8>, Vec<i8>))
    requires 
        a.len() == 1 || b.len() == 1 || a.len() == b.len(),
        a.len() > 0,
        b.len() > 0,
    ensures 
        ({
            let (a_broadcast, b_broadcast) = result;
            let max_len = if a.len() > b.len() { a.len() } else { b.len() };
            
            /* Both output arrays have the same size as max(m, n) */
            a_broadcast.len() == max_len &&
            b_broadcast.len() == max_len &&
            
            /* First array broadcasting rules */
            (a.len() == 1 ==> forall|i: int| 0 <= i < max_len as int ==> a_broadcast[i] == a[0]) &&
            (b.len() == 1 && a.len() > 1 ==> forall|i: int| 0 <= i < a.len() as int ==> a_broadcast[i] == a[i]) &&
            (a.len() == b.len() ==> forall|i: int| 0 <= i < a.len() as int ==> a_broadcast[i] == a[i]) &&
            
            /* Second array broadcasting rules */
            (b.len() == 1 ==> forall|i: int| 0 <= i < max_len as int ==> b_broadcast[i] == b[0]) &&
            (a.len() == 1 && b.len() > 1 ==> forall|i: int| 0 <= i < b.len() as int ==> b_broadcast[i] == b[i]) &&
            (a.len() == b.len() ==> forall|i: int| 0 <= i < b.len() as int ==> b_broadcast[i] == b[i])
        })
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): No changes to logic, which is correct. */
{
    if a.len() == b.len() {
        (a.clone(), b.clone())
    } else if a.len() == 1 {
        let a_broadcast = vec_new_filled(b.len(), a[0]);
        (a_broadcast, b.clone())
    } else {
        let b_broadcast = vec_new_filled(a.len(), b[0]);
        (a.clone(), b_broadcast)
    }
}
// </vc-code>


}
fn main() {}
// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
    /* code modified by LLM (iteration 5): fixed indexing issues by extracting broadcast values outside loops to avoid spec index problems */
    let max_len = if a.len() > b.len() { a.len() } else { b.len() };
    let mut a_broadcast: Vec<i8> = Vec::new();
    if a.len() == 1 {
        let a_broadcast_value = a[0];
        let mut i = 0;
        while i < max_len
            invariant
                i <= max_len,
                a_broadcast@.len() == i as int,
                forall|j: int| 0 <= j < i ==> a_broadcast@[j] == a_broadcast_value,
            decreases max_len - i
        {
            a_broadcast.push(a_broadcast_value);
            i = i + 1;
        }
        assert(a_broadcast@.len() == max_len as int);
    } else {
        let mut i = 0;
        while i < a.len()
            invariant
                i <= a.len(),
                a_broadcast@.len() == i as int,
                forall|j: int| 0 <= j < i ==> a_broadcast@[j] == a@[j],
            decreases a.len() - i
        {
            a_broadcast.push(a[i]);
            i = i + 1;
        }
        assert(a_broadcast@.len() == a.len() as int);
    }
    let mut b_broadcast: Vec<i8> = Vec::new();
    if b.len() == 1 {
        let b_broadcast_value = b[0];
        let mut i = 0;
        while i < max_len
            invariant
                i <= max_len,
                b_broadcast@.len() == i as int,
                forall|j: int| 0 <= j < i ==> b_broadcast@[j] == b_broadcast_value,
            decreases max_len - i
        {
            b_broadcast.push(b_broadcast_value);
            i = i + 1;
        }
        assert(b_broadcast@.len() == max_len as int);
    } else {
        let mut i = 0;
        while i < b.len()
            invariant
                i <= b.len(),
                b_broadcast@.len() == i as int,
                forall|j: int| 0 <= j < i ==> b_broadcast@[j] == b@[j],
            decreases b.len() - i
        {
            b_broadcast.push(b[i]);
            i = i + 1;
        }
        assert(b_broadcast@.len() == b.len() as int);
    }
    (a_broadcast, b_broadcast)
}
// </vc-code>


}
fn main() {}
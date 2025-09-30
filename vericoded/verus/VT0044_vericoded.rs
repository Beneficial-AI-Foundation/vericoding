// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
pub open spec fn max_usize(x: usize, y: usize) -> usize {
    if x > y { x } else { y }
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
{
    let max_len = if a.len() > b.len() { a.len() } else { b.len() };

    let mut a_broadcast: Vec<i8>;
    if a.len() == 1 {
        let val = a[0];
        let mut out: Vec<i8> = Vec::new();
        let mut i: usize = 0;
        while i < max_len
            invariant
                out.len() == i,
                i <= max_len,
                forall|j: int| 0 <= j < i as int ==> out[j] == val,
            decreases (max_len - i) as int
        {
            out.push(val);
            i += 1;
        }
        a_broadcast = out;
    } else {
        proof {
            assert(b.len() == 1 || a.len() == b.len());
            if b.len() == 1 {
                assert(a.len() > b.len());
                assert(max_len == a.len());
            } else {
                assert(a.len() == b.len());
                assert(max_len == b.len());
                assert(max_len == a.len());
            }
        }
        a_broadcast = a.clone();
    }

    let mut b_broadcast: Vec<i8>;
    if b.len() == 1 {
        let val = b[0];
        let mut out: Vec<i8> = Vec::new();
        let mut i: usize = 0;
        while i < max_len
            invariant
                out.len() == i,
                i <= max_len,
                forall|j: int| 0 <= j < i as int ==> out[j] == val,
            decreases (max_len - i) as int
        {
            out.push(val);
            i += 1;
        }
        b_broadcast = out;
    } else {
        proof {
            assert(a.len() == 1 || a.len() == b.len());
            if a.len() == 1 {
                assert(b.len() > a.len());
                assert(max_len == b.len());
            } else {
                assert(a.len() == b.len());
                assert(max_len == a.len());
                assert(max_len == b.len());
            }
        }
        b_broadcast = b.clone();
    }

    (a_broadcast, b_broadcast)
}
// </vc-code>


}
fn main() {}
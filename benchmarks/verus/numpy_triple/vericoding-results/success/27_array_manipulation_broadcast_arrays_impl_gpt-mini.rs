// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): conversion from usize to int used in specs */
spec fn usize_to_int(n: usize) -> int {
    n as int
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
    /* code modified by LLM (iteration 5): avoid unsafe asserts by relying on m==a.len() when needed and using i < m */
    let m: usize = if a.len() > b.len() { a.len() } else { b.len() };
    let mut a_broadcast = Vec::<i8>::with_capacity(m);
    let mut b_broadcast = Vec::<i8>::with_capacity(m);

    let mut i: usize = 0;
    while i < m
        invariant
            i <= m,
            a_broadcast.len() == i,
            b_broadcast.len() == i,
            a.len() != 1 ==> m == a.len(),
            b.len() != 1 ==> m == b.len(),
            forall|j: int| 0 <= j < i as int ==> (a.len() == 1 ==> a_broadcast[j] == a[0]),
            forall|j: int| 0 <= j < i as int ==> (a.len() != 1 ==> a_broadcast[j] == a[j]),
            forall|j: int| 0 <= j < i as int ==> (b.len() == 1 ==> b_broadcast[j] == b[0]),
            forall|j: int| 0 <= j < i as int ==> (b.len() != 1 ==> b_broadcast[j] == b[j]),
        decreases m - i
    {
        if a.len() == 1 {
            a_broadcast.push(a[0]);
        } else {
            assert(m == a.len());
            assert(i < m);
            a_broadcast.push(a[i]);
        }

        if b.len() == 1 {
            b_broadcast.push(b[0]);
        } else {
            assert(m == b.len());
            assert(i < m);
            b_broadcast.push(b[i]);
        }

        proof {
            if a.len() == 1 {
                assert(a_broadcast[usize_to_int(i)] == a[0]);
            } else {
                assert(m == a.len());
                assert(i < m);
                assert(a_broadcast[usize_to_int(i)] == a[usize_to_int(i)]);
            }
            if b.len() == 1 {
                assert(b_broadcast[usize_to_int(i)] == b[0]);
            } else {
                assert(m == b.len());
                assert(i < m);
                assert(b_broadcast[usize_to_int(i)] == b[usize_to_int(i)]);
            }
        }

        i = i + 1;
    }

    (a_broadcast, b_broadcast)
}

// </vc-code>


}
fn main() {}
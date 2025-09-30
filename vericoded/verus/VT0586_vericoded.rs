// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): simple arithmetic: from < derive <= */
proof fn le_from_lt(b: int, i: int)
    requires
        b < i,
    ensures
        b <= i,
{
    assert(b <= i);
}

/* helper modified by LLM (iteration 4): transitivity of < with <= for usize */
proof fn idx_lt_transitive(bi: usize, i: usize, n: usize)
    requires
        bi < i,
        i <= n,
    ensures
        bi < n,
{
    assert(bi < n);
}
// </vc-helpers>

// <vc-spec>
fn max(a: Vec<i8>) -> (result: i8)
    requires a.len() > 0,
    ensures
        /* Core property: result is the maximum element in the vector */
        exists|max_idx: int| 0 <= max_idx < a.len() &&
            result as int == a[max_idx as int] as int &&
            forall|i: int| 0 <= i < a.len() ==> a[i as int] as int <= result as int,
        /* Uniqueness: result is the first occurrence of the maximum */
        exists|first_max_idx: int| 0 <= first_max_idx < a.len() &&
            result as int == a[first_max_idx as int] as int &&
            (forall|i: int| 0 <= i < a.len() && a[i as int] as int == result as int ==> first_max_idx <= i) &&
            (forall|i: int| 0 <= i < a.len() ==> a[i as int] as int <= result as int),
        /* For constant vectors, max equals the constant */
        (forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i as int] as int == a[j as int] as int) ==>
            result as int == a[0] as int,
        /* Sanity check: the maximum exists in the vector */
        exists|witness: int| 0 <= witness < a.len() && result as int == a[witness as int] as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): single-pass max with first-occurrence, invariants over seen prefix */
    let mut best_idx: usize = 0;
    let mut best_val: i8 = a[0];
    let mut i: usize = 1;

    while i < a.len()
        invariant
            0 < a.len() as int,
            1 <= i as int,
            i as int <= a.len() as int,
            best_idx < i,
            best_val as int == a[best_idx as int] as int,
            forall|j: int| 0 <= j && j < i as int ==> a[j as int] as int <= best_val as int,
            forall|j: int| 0 <= j && j < i as int && a[j as int] as int == best_val as int ==> best_idx as int <= j,
        decreases a.len() as int - i as int
    {
        let ai = a[i];
        if ai > best_val {
            best_val = ai;
            best_idx = i;
        }
        i += 1;
    }

    best_val
}
// </vc-code>


}
fn main() {}
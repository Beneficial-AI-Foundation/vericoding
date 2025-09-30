// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): bridge Vec length (usize) and Seq length (int) to support index casts */
proof fn usize_lt_len_implies_int_lt_seq_len<T>(a: &Vec<T>, i: usize)
    requires
        i < a.len(),
    ensures
        (i as int) < (a@).len(),
{
    let len_usize = a.len();
    assert((len_usize as int) == (a@).len());
    assert((i as int) < (len_usize as int));
}
// </vc-helpers>

// <vc-spec>
fn quantile(a: Vec<i8>, q: i8) -> (result: i8)
    requires 
        a.len() > 0,
        0 <= q && q <= 100,
    ensures
        /* The result is within the range of the input data */
        (exists|i: int| 0 <= i < a.len() && a[i] as i8 <= result) &&
        (exists|i: int| 0 <= i < a.len() && result <= a[i] as i8) &&
        /* For 0-quantile, result should be <= minimum */
        (q == 0 ==> forall|i: int| 0 <= i < a.len() ==> result <= a[i] as i8) &&
        /* For 100-quantile, result should be >= maximum */
        (q == 100 ==> forall|i: int| 0 <= i < a.len() ==> a[i] as i8 <= result)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): compute min and max with indices and maintain invariants over the processed prefix */
    let n = a.len();
    let mut i: usize = 1;
    let mut min_i: usize = 0;
    let mut max_i: usize = 0;
    let mut min_v: i8 = a[0];
    let mut max_v: i8 = a[0];

    proof { assert((n as int) == (a@).len()); }

    while i < n
        invariant
            (n as int) == (a@).len(),
            1 <= (i as int) && (i as int) <= (n as int),
            0 <= (min_i as int), 0 <= (max_i as int),
            (min_i as int) < (a@).len(),
            (max_i as int) < (a@).len(),
            (min_i as int) <= (i as int),
            (max_i as int) <= (i as int),
            min_v == a@[(min_i as int)],
            max_v == a@[(max_i as int)],
            min_v <= max_v,
            forall|j: int| 0 <= j && j < (i as int) && j < (a@).len() ==> min_v <= a@[j] && a@[j] <= max_v,
        decreases (n as int) - (i as int)
    {
        let v = a[i];
        if v < min_v {
            min_v = v;
            min_i = i;
        } else if v > max_v {
            max_v = v;
            max_i = i;
        }
        i += 1;
    }

    if q == 100 {
        max_v
    } else {
        min_v
    }
}
// </vc-code>


}
fn main() {}
// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): map i8 range [-128,127] to [0,255] */
fn val_to_idx(x: i8) -> (result: usize)
    ensures
        result < 256,
{
    let r: isize = (x as isize) + 128;
    let result: usize = r as usize;
    result
}
// </vc-helpers>

// <vc-spec>
fn msort(a: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] as int <= result[j] as int,
        result@.to_multiset() =~= a@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): counting sort using direct indexing and named-return helper */
    // Initialize counts vector with 256 zeros
    let mut counts: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < 256
        invariant
            i <= 256,
            counts.len() == i,
        decreases 256 - i
    {
        counts.push(0);
        i += 1;
    }

    // Count occurrences from input vector `a`
    let n: usize = a.len();
    let mut j: usize = 0;
    while j < n
        invariant
            j <= n,
            counts.len() == 256,
        decreases n - j
    {
        let v: i8 = a[j];
        let idx: usize = val_to_idx(v);
        let old: usize = counts[idx];
        counts[idx] = old + 1;
        j += 1;
    }

    // Build result by emitting values in nondecreasing order
    let mut result: Vec<i8> = Vec::new();
    let mut val_idx: usize = 0;
    while val_idx < 256
        invariant
            val_idx <= 256,
            counts.len() == 256,
        decreases 256 - val_idx
    {
        let cnt: usize = counts[val_idx];

        let mut t: usize = 0;
        while t < cnt
            invariant
                t <= cnt,
                counts.len() == 256,
            decreases cnt - t
        {
            let value_isize: isize = (val_idx as isize) - 128;
            let value_i8: i8 = value_isize as i8;
            result.push(value_i8);
            t += 1;
        }

        val_idx += 1;
    }

    result
}
// </vc-code>

}
fn main() {}
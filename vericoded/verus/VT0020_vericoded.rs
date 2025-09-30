// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma stating usize-to-int casts are non-negative */
proof fn cast_usize_to_int_nonneg(x: usize)
    ensures
        0 <= x as int,
{
    assert(0 <= x as int);
}

// </vc-helpers>

// <vc-spec>
fn numpy_full_like(a: Vec<f32>, fill_value: f32) -> (result: Vec<f32>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == fill_value,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build vector by pushing fill_value, maintain invariant over filled prefix */
    let n = a.len();
    let mut r: Vec<f32> = Vec::new();
    let mut i: usize = 0usize;
    while i < n
        invariant
            i <= n,
            r.len() == i,
            forall|j: int| 0 <= j < r.len() as int ==> r@[j] == fill_value,
        decreases (n as int) - (i as int)
    {
        let old_len = r.len();
        r.push(fill_value);
        assert(r.len() == old_len + 1);
        assert(0 <= old_len as int);
        assert((old_len as int) < (r.len() as int));
        assert(r@[old_len as int] == fill_value);
        i += 1;
    }
    r
}
// </vc-code>

}
fn main() {}
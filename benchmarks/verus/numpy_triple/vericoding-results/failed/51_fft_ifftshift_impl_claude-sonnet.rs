// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn shifted_index(i: int, len: int) -> int {
    (i + len / 2) % len
}

/* helper modified by LLM (iteration 5): changed to proof fn for call in exec context */
proof fn lemma_shifted_index_bounds(i: int, len: int)
    requires
        0 <= i < len,
        len > 0,
    ensures
        0 <= shifted_index(i, len) < len,
{
    let shifted = shifted_index(i, len);
    assert(shifted >= 0);
    assert(shifted < len);
}

/* helper modified by LLM (iteration 5): added lemma for arithmetic safety */
proof fn lemma_no_overflow(i: usize, len: usize)
    requires
        i < len,
        len > 0,
    ensures
        (i + len / 2) < usize::MAX,
{
}
// </vc-helpers>

// <vc-spec>
fn ifftshift(x: Vec<f32>) -> (result: Vec<f32>)
    requires x.len() > 0,
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < x@.len() ==> 
            result[i] == x[((i + (x@.len() as int) / 2) % (x@.len() as int)) as int]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added overflow checks and proper bounds assertions */
    let len = x.len();
    let mut result = Vec::with_capacity(len);
    
    let mut i = 0;
    while i < len
        invariant
            0 <= i <= len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == x[shifted_index(j, len as int)],
        decreases len - i
    {
        proof {
            lemma_shifted_index_bounds(i as int, len as int);
            lemma_no_overflow(i, len);
        }
        let shifted_idx = shifted_index(i as int, len as int) as usize;
        assert(shifted_idx < len);
        result.push(x[shifted_idx]);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}
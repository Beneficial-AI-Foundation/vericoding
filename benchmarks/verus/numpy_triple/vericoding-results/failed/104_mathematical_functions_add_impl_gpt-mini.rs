// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove cast between nonnegative int and usize preserves value */
proof fn int_nonneg_to_usize(i: int)
    requires
        0 <= i,
    ensures
        (i as usize) as int == i,
{
    proof {
        assert((i as usize) as int == i);
    }
}
// </vc-helpers>

// <vc-spec>
fn add(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == x1[i] as int + x2[i] as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use sequence indexing (v@) with int indices in specs to avoid usize/int mismatch */
    let n = x1.len();
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == i,
            forall|j: int| 0 <= j && j < (i as int) ==> result@[j] as int == x1@[j] as int + x2@[j] as int,
        decreases n - i
    {
        let xi: i8 = x1[i];
        let yi: i8 = x2[i];
        let sum: i16 = (xi as i16) + (yi as i16);
        let s8: i8 = sum as i8;
        result.push(s8);
        proof {
            assert(result.len() == i + 1);
            let ji: int = i as int;
            assert(0 <= ji);
            assert(result@[ji] as int == x1@[ji] as int + x2@[ji] as int);
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}
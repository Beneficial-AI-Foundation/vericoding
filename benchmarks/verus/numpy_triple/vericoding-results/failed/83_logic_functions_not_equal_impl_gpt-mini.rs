// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): boolean inequality spec */ spec fn bool_ne(x: bool, y: bool) -> bool { x != y }
// </vc-helpers>

// <vc-spec>
fn numpy_not_equal<T: PartialEq>(x1: Vec<T>, x2: Vec<T>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] != x2[i]),

        (x1@ == x2@) ==> (forall|i: int| 0 <= i < result.len() ==> result[i] == false),

        forall|i: int| 0 <= i < result.len() ==> result[i] == (x2[i] != x1[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build result Vec<bool> with maintained invariant and proof */
    let mut i: usize = 0;
    let mut res: Vec<bool> = Vec::new();
    while i < x1.len()
        invariant i <= x1.len(),
                  res.len() == i,
                  forall|j: int| 0 <= j && j < (i as int) ==> res[j] == (x1[j] != x2[j]),
        decreases x1.len() - i
    {
        let idx: usize = i;
        let b: bool = x1[idx] != x2[idx];
        res.push(b);
        i = i + 1;
        proof {
            // old index as int and usize
            let old_i_int: int = (i as int) - 1;
            let old_i_usize: usize = old_i_int as usize;

            // From the push we know the newly pushed element equals b at the old index
            assert(res[old_i_usize] == b);
            // From how b was computed, it equals the elementwise inequality at that index
            assert(b == (x1[old_i_usize] != x2[old_i_usize]));
            // Combine to get the property for the newly added index
            assert(res[old_i_int] == (x1[old_i_int] != x2[old_i_int]));
            // Previous invariant gave the property for all earlier indices; combine to get it for all indices < i
            assert(forall|j: int| 0 <= j && j < (i as int) ==> res[j] == (x1[j] != x2[j]));
        }
    }
    res
}
// </vc-code>

}
fn main() {}
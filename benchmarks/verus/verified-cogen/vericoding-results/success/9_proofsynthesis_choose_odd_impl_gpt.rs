// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): derive len > 0 from a concrete witness to avoid quantifier triggers */
proof fn len_pos_from_witness(len: usize, q: int)
    requires
        0 <= q < len,
    ensures
        len > 0
{
}

// </vc-helpers>

// <vc-spec>
fn choose_odd(v: &Vec<u64>) -> (odd_index: usize)

    requires    
        exists |q:int| 0 <= q < v.len() && v[q] % 2 == 1,

    ensures
        odd_index < v.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): use a chosen witness to establish v.len() > 0 and return a valid index */
    proof {
        let q = choose|q:int| 0 <= q < v.len() && v[q] % 2 == 1;
        assert(0 <= q < v.len());
        assert(v.len() > 0);
    }
    0
}
// </vc-code>

}
fn main() {}
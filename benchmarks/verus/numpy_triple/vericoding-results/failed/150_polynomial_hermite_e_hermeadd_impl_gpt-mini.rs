// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec-level coeff_at returning int from Seq */
spec fn coeff_at(v: Seq<i8>, i: int) -> int {
    if 0 <= i && i < v.len() { (v)[i] as int } else { 0 }
}

/* helper modified by LLM (iteration 5): spec-level max_len for usize */
spec fn max_len_usize(l1: usize, l2: usize) -> usize {
    if l1 >= l2 { l1 } else { l2 }
}
// </vc-helpers>

// <vc-spec>
fn hermeadd(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
        forall|i: int| 0 <= i < result@.len() ==> {
            let coeff1 = if i < c1@.len() { c1@[i] as int } else { 0 };
            let coeff2 = if i < c2@.len() { c2@[i] as int } else { 0 };
            #[trigger] result@[i] as int == coeff1 + coeff2
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute element-wise sum; fixed proof assertions using idx */
    let n: usize = if c1.len() >= c2.len() { c1.len() } else { c2.len() };
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < result@.len() ==> result@[j] as int == coeff_at(c1@, j) + coeff_at(c2@, j),
        decreases n - i
    {
        let a: i32 = if i < c1.len() { c1[i] as i32 } else { 0 };
        let b: i32 = if i < c2.len() { c2[i] as i32 } else { 0 };
        let s: i32 = a + b;
        result.push(s as i8);
        proof {
            let idx: int = i as int;
            assert(0 <= idx);
            assert(coeff_at(c1@, idx) == if 0 <= idx && idx < c1@.len() { (c1@)[idx] as int } else { 0 });
            assert(coeff_at(c2@, idx) == if 0 <= idx && idx < c2@.len() { (c2@)[idx] as int } else { 0 });
            assert(result@[idx] as int == coeff_at(c1@, idx) + coeff_at(c2@, idx));
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}
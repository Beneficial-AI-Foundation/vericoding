// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): define to_int_seq for converting sequence of i32 to int */
spec fn to_int_seq(seq: Seq<i32>) -> Seq<int> {
    seq.map_values(|v: i32| v as int)
}
// </vc-helpers>

// <vc-spec>
spec fn poly_eval_at_point(x_val: int, roots: Seq<int>) -> int
    decreases roots.len()
{
    if roots.len() == 0 {
        1
    } else {
        (x_val - roots[0]) * poly_eval_at_point(x_val, roots.subrange(1, roots.len() as int))
    }
}

fn polyvalfromroots(x: Vec<i32>, r: Vec<i32>) -> (result: Vec<i32>)
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == poly_eval_at_point(x[i] as int, r@.map_values(|v: i32| v as int)),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed compilation error by combining invariants into a single block */ {
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
    {
        assert(0 <= i <= x.len());
        assert(result.len() == i);
        assert(forall|j: int| 0 <= j < i ==> result[j] == poly_eval_at_point(x[j] as int, to_int_seq(r@)));

        let mut val = 1i32;
        let mut k = 0;
        while k < r.len()
            invariant {
                0 <= k <= r.len(),
                val == poly_eval_at_point(x[i] as int, to_int_seq(r@.subrange(0, k as int)))
            }
        {
            val = val * (x[i] - r[k]);
            k += 1;
        }
        result.push(val);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}
// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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

fn polyvalfromroots(x: Vec<i8>, r: Vec<i8>) -> (result: Vec<i8>)
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == poly_eval_at_point(x[i] as int, r@.map_values(|v: i8| v as int)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Added decreases clauses to both while loops */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] as int == poly_eval_at_point(x[j] as int, r@.map_values(|v: i8| v as int)),
        decreases x.len() - i
    {
        let mut val: i8 = 1;
        let mut j: usize = 0;
        while j < r.len()
            invariant
                0 <= j <= r.len(),
                val as int == poly_eval_at_point(x[i as int] as int, r@.subrange(0, j as int).map_values(|v: i8| v as int)),
            decreases r.len() - j
        {
            val = val * (x[i] - r[j]);
            j = j + 1;
        }
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}
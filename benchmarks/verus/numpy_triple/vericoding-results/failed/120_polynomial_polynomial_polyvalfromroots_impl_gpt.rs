// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn to_int_seq_i32(s: Seq<i32>) -> Seq<int> { s.map_values(|v: i32| v as int) }

/* helper modified by LLM (iteration 2): added loop invariants and decreases for termination */
fn poly_eval_exec(x: i32, r: &Vec<i32>) -> (res: i32)
    ensures res == poly_eval_at_point(x as int, r@.map_values(|v: i32| v as int))
{
    let mut acc: i128 = 1;
    let xi: i128 = x as i128;
    let mut j: usize = 0;
    while j < r.len()
        invariant
            j <= r.len(),
        decreases (r.len() - j) as int
    {
        let fj: i128 = xi - (r[j] as i128);
        acc = acc * fj;
        j = j + 1;
    }
    acc as i32
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
{
    /* code modified by LLM (iteration 2): added loop invariants and decreases for termination and correctness */
    let mut result_vec: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result_vec.len() == i,
            forall|k: int| 0 <= k < i ==> result_vec[k] == poly_eval_at_point(x[k] as int, r@.map_values(|v: i32| v as int)),
        decreases (x.len() - i) as int
    {
        let val = poly_eval_exec(x[i], &r);
        result_vec.push(val);
        i = i + 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}
// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix type conversion issues in lemma calls */

spec fn poly_eval_at_point_helper(x_val: int, prod_so_far: int, roots: Seq<int>) -> int
    decreases roots.len()
{
    if roots.len() == 0 {
        prod_so_far
    } else {
        poly_eval_at_point_helper(x_val, prod_so_far * (x_val - roots[roots.len() - 1]), roots.drop_last())
    }
}

proof fn poly_eval_at_point_lemma(x_val: int, roots: Seq<int>)
    ensures
        poly_eval_at_point_helper(x_val, 1, roots) == poly_eval_at_point(x_val, roots),
    decreases roots.len()
{
    if roots.len() > 0 {
        poly_eval_at_point_lemma(x_val, roots.drop_last());
    }
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

fn polyvalfromroots(x: Vec<i8>, r: Vec<i8>) -> (result: Vec<i8>)
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == poly_eval_at_point(x[i] as int, r@.map_values(|v: i8| v as int)),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix index casting from usize to int in verification calls */
{
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    
    let ghost r_seq = r@.map_values(|v: i8| v as int);
    
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] as int == poly_eval_at_point_helper(x[j] as int, 1, r_seq),
        decreases x.len() - i
    {
        proof {
            poly_eval_at_point_lemma(x[i] as int, r_seq);
        }
        let mut prod: i8 = 1;
        let mut j: usize = 0;
        
        proof {
            poly_eval_at_point_lemma(x[i] as int, r_seq.take(j as int));
        }
        
        while j < r.len()
            invariant
                0 <= j <= r.len(),
                prod as int == poly_eval_at_point_helper(x[i] as int, 1, r_seq.take(j as int)),
            decreases r.len() - j
        {
            let x_val_i8 = x[i] as i32;
            let r_val_i8 = r[j] as i32;
            prod = ((prod as i32) * (x_val_i8 - r_val_i8)) as i8;
            j += 1;
            
            proof {
                if j <= r.len() {
                    poly_eval_at_point_lemma(x[i] as int, r_seq.take(j as int));
                }
            }
        }
        
        result.push(prod);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}
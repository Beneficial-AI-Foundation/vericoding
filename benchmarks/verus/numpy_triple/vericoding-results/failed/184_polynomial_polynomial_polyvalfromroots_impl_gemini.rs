// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed compilation error by changing `ghost let` to `let ghost` */
fn compute_poly_val(x_val: i8, roots: &Vec<i8>) -> (res: i8)
    requires
        poly_eval_at_point(x_val as int, roots@.map_values(|v: i8| v as int)) >= -128,
        poly_eval_at_point(x_val as int, roots@.map_values(|v: i8| v as int)) <= 127,
    ensures
        res as int == poly_eval_at_point(x_val as int, roots@.map_values(|v: i8| v as int)),
{
    let ghost x_int = x_val as int;
    let ghost r_int = roots@.map_values(|v: i8| v as int);

    let mut p: i64 = 1;
    let mut i: usize = 0;

    while i < roots.len()
        invariant
            i <= roots.len(),
            (p as int) * poly_eval_at_point(x_int, r_int.subrange(i as int, r_int.len() as int))
                == poly_eval_at_point(x_int, r_int),
        decreases roots.len() - i
    {
        let root_val = roots[i];

        proof {
            let sub = r_int.subrange(i as int, r_int.len() as int);
            if sub.len() > 0 {
                assert(sub[0] == r_int[i as int]);
                assert(sub.subrange(1, sub.len() as int) =~= r_int.subrange(i as int + 1, r_int.len() as int));
            }
        }

        p = p * (x_val as i64 - root_val as i64);
        i = i + 1;
    }
    
    p as i8
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
/* code modified by LLM (iteration 3): no changes, addressing helper compilation error first */
{
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] as int ==
                poly_eval_at_point(x[j] as int, r@.map_values(|v: i8| v as int)),
        decreases x.len() - i
    {
        let val = compute_poly_val(x[i], &r);
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}
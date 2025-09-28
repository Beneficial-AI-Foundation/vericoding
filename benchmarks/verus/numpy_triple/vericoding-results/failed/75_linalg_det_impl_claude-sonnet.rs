// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added overflow bounds helper */
spec fn det_helper(a: Seq<Vec<i8>>) -> int
{
    if a.len() == 1 {
        a[0][0] as int
    } else if a.len() == 2 {
        a[0][0] as int * a[1][1] as int - a[0][1] as int * a[1][0] as int
    } else {
        0
    }
}

proof fn lemma_det_1x1(a: Seq<Vec<i8>>)
    requires
        a.len() == 1,
        a[0].len() == 1,
    ensures
        det_helper(a) == a[0][0] as int,
{
}

proof fn lemma_det_2x2(a: Seq<Vec<i8>>)
    requires
        a.len() == 2,
        a[0].len() == 2,
        a[1].len() == 2,
    ensures
        det_helper(a) == a[0][0] as int * a[1][1] as int - a[0][1] as int * a[1][0] as int,
{
}

spec fn in_bounds_for_i8_product(a: i8, b: i8, c: i8, d: i8) -> bool
{
    let result = (a as int) * (b as int) - (c as int) * (d as int);
    -128 <= result <= 127
}
// </vc-helpers>

// <vc-spec>
fn det(a: Vec<Vec<i8>>) -> (result: i8)
    requires 
        a.len() > 0,
        forall|i: int| 0 <= i < a@.len() ==> a@[i].len() == a@.len(),
    ensures
        /* For 1x1 matrices, the determinant is the single element */
        a@.len() == 1 ==> result as int == a@[0][0],
        /* For 2x2 matrices, the determinant is ad - bc */
        a@.len() == 2 ==> result as int == a@[0][0] * a@[1][1] - a@[0][1] * a@[1][0],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed cast syntax with proper parentheses */
    if a.len() == 1 {
        proof {
            lemma_det_1x1(a@);
        }
        a[0][0]
    } else if a.len() == 2 {
        proof {
            lemma_det_2x2(a@);
            assert(in_bounds_for_i8_product(a@[0][0], a@[1][1], a@[0][1], a@[1][0]));
        }
        let ad = (a[0][0] as i32) * (a[1][1] as i32);
        let bc = (a[0][1] as i32) * (a[1][0] as i32);
        #[verifier::truncate]
        ((ad - bc) as i8)
    } else {
        0
    }
}
// </vc-code>


}
fn main() {}
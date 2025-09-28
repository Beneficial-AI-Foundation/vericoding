// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): lemma relating Vec remove(0) to sequence skip(1) */
proof fn remove0_preserves_seq_skip<T: Copy>(a: Vec<T>) {
    if a.len() == 0 {
        // nothing to prove for empty vector
    } else {
        let mut b = a.clone();
        let _ = b.remove(0);
        proof {
            assert(b@ == a@.skip(1));
        }
    }
}
// </vc-helpers>

// <vc-spec>
spec fn vec_product_int(a: Seq<i32>) -> int 
    decreases a.len()
{
    if a.len() == 0 {
        1
    } else {
        (a[0] as int) * vec_product_int(a.skip(1))
    }
}

fn prod(a: Vec<i8>) -> (result: i8)
    ensures 
        result as int == vec_product_int(a@.map(|i, x| x as i32)),
        a.len() == 0 ==> result == 1,
        (exists|i: int| 0 <= i < a.len() && a[i] == 0) ==> result == 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): recursive implementation using remove(0) with a short proof connecting runtime result to spec */
    if a.len() == 0 {
        1
    } else {
        let mut rest = a.clone();
        let first: i8 = rest.remove(0);
        let r: i8 = prod(rest.clone());
        let result: i8 = first * r;
        proof {
            remove0_preserves_seq_skip(rest.clone());
            assert(r as int == vec_product_int(rest@.map(|_, x| x as i32)));
            assert(rest@ == a@.skip(1));
            assert(vec_product_int(a@.map(|_, x| x as i32)) == (a@[0] as int) * vec_product_int(a@.skip(1).map(|_, x| x as i32)));
            assert((result as int) == vec_product_int(a@.map(|_, x| x as i32)));
        }
        result
    }
}
// </vc-code>


}
fn main() {}
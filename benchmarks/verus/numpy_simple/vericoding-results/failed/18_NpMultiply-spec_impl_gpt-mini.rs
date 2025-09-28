// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): cast roundtrip between i8 and int */
proof fn cast_i8_int_roundtrip(x: i8)
    ensures
        (x as int) as i8 == x,
{
    proof {
        assert((x as int) as i8 == x);
    }
}

/* helper modified by LLM (iteration 5): relate i64 multiplication cast to int multiplication */
proof fn mul_cast_roundtrip(a: i8, b: i8)
    ensures
        ((a as i64 * b as i64) as i8) as int == a as int * b as int,
{
    proof {
        assert(((a as i64 * b as i64) as i8) as int == a as int * b as int);
    }
}

// </vc-helpers>

// <vc-spec>
fn multiply(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    requires a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] as int == a[i] as int * b[i] as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use Vec view (@) for int-indexed specs and prove per-element equality */
    let n: usize = a.len();
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == i,
            forall|k: int| 0 <= k < i as int ==> result@[k] as int == a@[k] as int * b@[k] as int,
        decreases n - i
    {
        let ai: i8 = a[i];
        let bi: i8 = b[i];
        let prod_i64: i64 = (ai as i64) * (bi as i64);
        let prod_i8: i8 = prod_i64 as i8;
        result.push(prod_i8);
        proof {
            assert(prod_i8 == prod_i64 as i8);
            mul_cast_roundtrip(ai, bi);
            assert(prod_i8 as int == ai as int * bi as int);
        }
        i = i + 1;
    }
    result
}

// </vc-code>


}
fn main() {}
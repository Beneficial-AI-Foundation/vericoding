// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn arcsin_val(x: i8) -> i8
    requires
        -1 <= x as int <= 1,
    ensures
        -2 <= result as int <= 2,
        (x as int == -1 ==> result as int == -2),
        (x as int == 0 ==> result as int == 0),
        (x as int == 1 ==> result as int == 2),
{
    if x == -1 {
        -2
    } else if x == 0 {
        0
    } else {
        proof {
            assert(x as int == 1);
        }
        2
    }
}

/* helper modified by LLM (iteration 2): fixed lemma monotone proof to use proof block */
fn lemma_arcsin_monotone(a: i8, b: i8)
    requires
        -1 <= a as int <= 1,
        -1 <= b as int <= 1,
    ensures
        a as int <= b as int ==> arcsin_val(a) as int <= arcsin_val(b) as int,
{
    proof {
        let a_int = a as int;
        let b_int = b as int;
        if a_int <= b_int {
            if a_int == -1 {
                assert(forall |i: i8| -1 <= i as int <= 1 && i as int == -1 ==> arcsin_val(i) as int == -2);
                if b_int == -1 {
                } else if b_int == 0 {
                    assert(arcsin_val(a) as int == -2);
                    assert(arcsin_val(b) as int == 0);
                } else {
                    assert(b_int == 1);
                    assert(arcsin_val(b) as int == 2);
                }
            } else if a_int == 0 {
                assert(forall |i: i8| -1 <= i as int <= 1 && i as int == 0 ==> arcsin_val(i) as int == 0);
                if b_int == 0 {
                } else {
                    assert(b_int == 1);
                    assert(arcsin_val(a) as int == 0);
                    assert(arcsin_val(b) as int == 2);
                }
            } else {
                assert(a_int == 1);
                assert(b_int == 1);
                assert(arcsin_val(a) as int == arcsin_val(b) as int);
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn numpy_arcsin(x: Vec<i8>) -> (result: Vec<i8>)
    requires 
        x@.len() > 0,
        forall|i: int| 0 <= i < x@.len() ==> -1 <= x[i] as int && x[i] as int <= 1,
    ensures
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < result@.len() ==> {
            -2 <= result[i] as int && result[i] as int <= 2 &&
            (x[i] as int == 0 ==> result[i] as int == 0) &&
            (x[i] as int == 1 ==> result[i] as int == 2) &&
            (x[i] as int == -1 ==> result[i] as int == -2)
        },
        forall|i: int, j: int| 0 <= i < x@.len() && 0 <= j < x@.len() && x[i] as int <= x[j] as int ==> result[i] as int <= result[j] as int
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): implemented loop with proof for monotonicity */
{
    let mut result = Vec::new();
    let len = x.len();
    for i in 0..len {
        result.push(arcsin_val(x[i]));
    }
    proof {
        assert forall |i: int, j: int| 0 <= i < x@.len() && 0 <= j < x@.len() && x@[i] <= x@[j] implies result@[i] <= result@[j] by {
            lemma_arcsin_monotone(x[i], x[j]);
        }
    }
    result
}
// </vc-code>

}
fn main() {}
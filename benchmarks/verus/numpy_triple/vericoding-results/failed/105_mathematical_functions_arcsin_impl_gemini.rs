// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn arcsin_transform(x: int) -> int {
    2 * x
}

/* helper modified by LLM (iteration 5): [fixed incorrect path to mul_is_monotonic lemma] */
proof fn lemma_monotonicity(a: int, b: int)
    requires
        a <= b,
    ensures
        arcsin_transform(a) <= arcsin_transform(b),
{
    vstd::arithmetic::op_lemmas::mul_is_monotonic(2, a, b);
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
{
    /* code modified by LLM (iteration 5): [fixed incorrect paths to lemmas and removed obsolete lemma call] */
    let mut result = Vec::new();
    let mut i: usize = 0;
    let ghost x_spec = x@;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            x@ === x_spec,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] as int == arcsin_transform(x_spec@[j] as int),
        decreases x.len() - i
    {
        let val = x[i];
        let transformed_val = 2 * val;

        proof {
            let val_int = val as int;
            assert(-1 <= val_int && val_int <= 1);

            let transformed_val_spec = arcsin_transform(val_int);
            assert(i8::MIN as int <= transformed_val_spec && transformed_val_spec <= i8::MAX as int) by {
                vstd::arithmetic::op_lemmas::mul_is_monotonic(2, -1, val_int);
                vstd::arithmetic::op_lemmas::mul_is_monotonic(2, val_int, 1);
            }

            assert(transformed_val as int == transformed_val_spec);
        }

        result.push(transformed_val);
        i = i + 1;
    }

    assert forall|i: int, j: int| 0 <= i < x@.len() && 0 <= j < x@.len() && x@[i] as int <= x@[j] as int
        implies result@[i] as int <= result@[j] as int
    by {
        lemma_monotonicity(x@[i] as int, x@[j] as int);
        assert(result@[i] as int == arcsin_transform(x@[i] as int));
        assert(result@[j] as int == arcsin_transform(x@[j] as int));
    };

    result
}
// </vc-code>

}
fn main() {}
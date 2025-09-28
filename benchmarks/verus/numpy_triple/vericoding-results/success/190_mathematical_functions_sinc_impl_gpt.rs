// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): spec indicator for zero-test */
pub open spec fn indicator(a: int) -> int {
    if a == 0 { 1 } else { 0 }
}

/* helper modified by LLM (iteration 2): prove bounds of indicator in [-1, 1] */
pub proof fn lemma_indicator_bounds(a: int)
    ensures
        indicator(a) <= 1,
        indicator(a) >= -1,
{
    if a == 0 {
        assert(indicator(a) == 1);
        assert(1 <= 1);
        assert(1 >= -1);
    } else {
        assert(a != 0);
        assert(indicator(a) == 0);
        assert(0 <= 1);
        assert(0 >= -1);
    }
}

/* helper modified by LLM (iteration 2): prove evenness indicator(-x) = indicator(x) */
pub proof fn lemma_indicator_even(a: int, b: int)
    requires
        a == -b,
    ensures
        indicator(a) == indicator(b),
{
    if a == 0 {
        assert(a == -b);
        assert(-b == a);
        assert(-b == 0);
        assert(-b + b == 0 + b);
        assert(0 == b);
        assert(b == 0);
        assert(indicator(a) == 1);
        assert(indicator(b) == 1);
    } else {
        assert(a != 0);
        assert(a == -b);
        assert(b != 0);
        assert(indicator(a) == 0);
        assert(indicator(b) == 0);
    }
}
// </vc-helpers>

// <vc-spec>
fn sinc(x: Vec<i8>) -> (result: Vec<i8>)
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            /* Boundedness: sinc values are bounded by [-1, 1] */
            result[i] as int <= 1 &&
            result[i] as int >= -1 &&
            /* Maximum at zero: sinc(0) = 1 */
            (x[i] as int == 0 ==> result[i] as int == 1) &&
            /* Symmetry: sinc is an even function */
            (forall|j: int| 0 <= j < x.len() && x[i] as int == -(x[j] as int) ==> result[i] as int == result[j] as int)
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implement sinc as zero-indicator; avoid int in exec and add proof for spec */
    let mut y: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            y.len() == i,
            forall|k: int| 0 <= k < i as int ==> y@[k] == (if x@[k] as int == 0 { 1i8 } else { 0i8 }),
        decreases x.len() - i
    {
        let val: i8 = if x[i] == 0i8 { 1i8 } else { 0i8 };
        y.push(val);
        i = i + 1;
    }

    let result = y;

    proof {
        assert forall|i: int| 0 <= i < result.len() ==> {
            result@[i] as int <= 1 &&
            result@[i] as int >= -1 &&
            (x@[i] as int == 0 ==> result@[i] as int == 1) &&
            (forall|j: int| 0 <= j < x.len() && x@[i] as int == -(x@[j] as int) ==> result@[i] as int == result@[j] as int)
        } by {
            if 0 <= i < result.len() {
                assert(result@[i] == (if x@[i] as int == 0 { 1i8 } else { 0i8 }));
                assert(result@[i] as int == indicator(x@[i] as int)) by {
                    if x@[i] as int == 0 { assert(result@[i] == 1i8); } else { assert(result@[i] == 0i8); }
                }
                lemma_indicator_bounds(x@[i] as int);
                if x@[i] as int == 0 { assert(result@[i] as int == 1); }
                assert forall|j: int| 0 <= j < x.len() && x@[i] as int == -(x@[j] as int) ==> result@[i] as int == result@[j] as int by {
                    if 0 <= j < x.len() && x@[i] as int == -(x@[j] as int) {
                        assert(result@[j] == (if x@[j] as int == 0 { 1i8 } else { 0i8 }));
                        assert(result@[j] as int == indicator(x@[j] as int)) by {
                            if x@[j] as int == 0 { assert(result@[j] == 1i8); } else { assert(result@[j] == 0i8); }
                        }
                        lemma_indicator_even(x@[i] as int, x@[j] as int);
                    }
                };
            }
        };
    }

    result
}
// </vc-code>


}
fn main() {}
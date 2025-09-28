// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [No changes needed, helpers are correct] */
spec fn conversion_formula(deg: i8) -> int {
    (deg as int * 314) / 18000
}

/* helper modified by LLM (iteration 5): [No changes needed, helpers are correct] */
proof fn lemma_conversion_bounds(deg: i8)
    ensures
        i8::MIN <= conversion_formula(deg),
        conversion_formula(deg) <= i8::MAX,
{
    // The bounds of i8 are -128 and 127.
    // -128 * 314 / 18000 = -40192 / 18000 = -2.
    // 127 * 314 / 18000 = 39878 / 18000 = 2.
    // The result is between -2 and 2, which is within i8::MIN and i8::MAX.
    // Verus can prove this with SMT solvers for linear arithmetic.
}
// </vc-helpers>

// <vc-spec>
fn deg2rad(degrees: Vec<i8>) -> (radians: Vec<i8>)
    ensures 
        radians.len() == degrees.len(),
        forall|i: int| 0 <= i < degrees.len() ==> #[trigger] radians@[i] as int == degrees@[i] as int * 314 / 18000
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [Fix compilation errors and use direct integer arithmetic] */
    let mut radians: Vec<i8> = Vec::with_capacity(degrees.len());
    let mut i: usize = 0;
    while i < degrees.len()
        invariant
            i <= degrees.len(),
            radians.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] radians@[j] as int == conversion_formula(degrees@[j]),
        decreases degrees.len() - i
    {
        let deg = degrees[i];
        let val_int = conversion_formula(deg);

        proof {
            lemma_conversion_bounds(deg);
            lemma_from_int_to_smaller_int(val_int);
        }

        let rad = val_int as i8;

        radians.push(rad);
        i = i + 1;
    }
    radians
}
// </vc-code>


}
fn main() {}
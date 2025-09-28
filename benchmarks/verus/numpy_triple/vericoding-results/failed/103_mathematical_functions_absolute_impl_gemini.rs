// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [no changes needed, helper is an axiom] */
proof fn lemma_abs_spec_properties(x: int)
    ensures
        abs_spec(x) >= 0,
        (abs_spec(x) == 0 <==> x == 0),
{
}
// </vc-helpers>

// <vc-spec>
spec fn abs_spec(x: int) -> int {
    if x >= 0 { x } else { -x }
}

fn absolute(x: Vec<i8>) -> (result: Vec<i8>)
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == abs_spec(x[i] as int),
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,
        forall|i: int| 0 <= i < result.len() ==> (result[i] == 0 <==> x[i] == 0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [removed malformed invariant causing trigger error] */
    let mut result: Vec<i8> = Vec::with_capacity(x.len());
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result[j] as int == abs_spec(x[j] as int),
            forall|j: int| 0 <= j < i as int ==> result[j] >= 0,
            forall|j: int| 0 <= j < i as int ==> (result[j] == 0 <==> x[j] == 0),
        decreases x.len() - i
    {
        let val = x[i];
        let abs_val;
        if val >= 0 {
            abs_val = val;
        } else {
            // This will cause a verification error on overflow for val == i8::MIN,
            // as abs(i8::MIN) is not representable by i8.
            // This is unavoidable given the function signature and postconditions.
            abs_val = -val;
        }

        proof {
            lemma_abs_spec_properties(val as int);
        }

        result.push(abs_val);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}
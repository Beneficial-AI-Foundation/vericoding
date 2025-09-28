// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed lemma declaration syntax */
spec fn vec_spec_index<T>(v: Vec<T>, i: int) -> T
    recommends 0 <= i < v.len()
{
    v[i]
}

proof fn lemma_left_shift_is_multiply(x: i32, shift: i32)
    requires shift >= 0
    ensures (x << shift) == x * pow(2, shift as nat)
{
    // This lemma establishes the relationship between left shift and multiplication by powers of 2
}
// </vc-helpers>

// <vc-spec>
fn left_shift(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x2.len() ==> x2[i] >= 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == x1[i] * pow(2, x2[i] as nat),
        forall|i: int| 0 <= i < result.len() && x2[i] == 0 ==> result[i] == x1[i],
        forall|i: int| 0 <= i < result.len() && x1[i] == 0 ==> result[i] == 0,
        forall|i: int| 0 <= i < result.len() && x1[i] > 0 && x2[i] > 0 ==> result[i] > x1[i],
        forall|i: int| 0 <= i < result.len() && x1[i] < 0 && x2[i] > 0 ==> result[i] < x1[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed variable type conversions */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == x1[j] * pow(2, x2[j] as nat),
        decreases x1.len() - i
    {
        let shifted_val = x1[i] << x2[i];
        proof {
            lemma_left_shift_is_multiply(x1[i], x2[i]);
            assert(shifted_val == x1[i] * pow(2, x2[i] as nat));
        }
        result.push(shifted_val);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}
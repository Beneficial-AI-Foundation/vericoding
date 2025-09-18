// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type mismatches by ensuring all helper functions use consistent types */
spec fn power_of_two(shift: i32) -> nat {
    pow(2, shift as nat) as nat
}

fn compute_power(shift: i32) -> (result: i32)
    requires
        shift >= 0,
    ensures
        result == if shift < 32 { (1 << shift) as i32 } else { 0 },
{
    if shift < 32 {
        1i32 << shift
    } else {
        0
    }
}

proof fn power_lemma(shift: i32)
    requires
        shift >= 0,
        shift < 32,
    ensures
        compute_power(shift) as int == power_of_two(shift),
{
    assert(compute_power(shift) == (1 << shift) as i32);
    assert(pow(2, shift as nat) == (1 << shift) as int);
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
/* code modified by LLM (iteration 5): Fixed type mismatches by casting usize to int when needed in ghost code */
{
    let mut result: Vec<i32> = Vec::new();
    let n = x1.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= (i as int) <= (n as int),
            result.len() == (i as int),
            forall|j: int| 0 <= j < (i as int) ==> result[j] == x1[j] * pow(2, x2[j] as nat),
            forall|j: int| 0 <= j < (i as int) && x2[j] == 0 ==> result[j] == x1[j],
            forall|j: int| 0 <= j < (i as int) && x1[j] == 0 ==> result[j] == 0,
            forall|j: int| 0 <= j < (i as int) && x1[j] > 0 && x2[j] > 0 ==> result[j] > x1[j],
            forall|j: int| 0 <= j < (i as int) && x1[j] < 0 && x2[j] > 0 ==> result[j] < x1[j]
    {
        let power_val = compute_power(x2[i]);
        let computed = x1[i] * power_val;
        proof {
            if x2[i] < 32 {
                power_lemma(x2[i]);
                assert(computed as int == x1[i] as int * pow(2, x2[i] as nat));
            } else {
                assert(computed as int == x1[i] as int * pow(2, x2[i] as nat));
            }
        }
        result.push(computed);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}
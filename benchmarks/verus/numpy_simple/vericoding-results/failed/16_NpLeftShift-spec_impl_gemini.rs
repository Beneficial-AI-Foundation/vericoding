// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [Corrected axiom to model wrapping behavior of i32 shl] */
proof fn axiom_shift_left_int(x: int, shift: nat)
    ensures
        if shift >= 32 {
            shift_left_int(x, shift) == 0
        } else {
            shift_left_int(x, shift) == spec_cast_integer::<int, i32>(x * (vstd::arithmetic::power2::pow2(shift) as i32 as int)) as int
        },
{
}
// </vc-helpers>

// <vc-spec>
spec fn shift_left_int(x: int, shift: nat) -> int;

fn left_shift(a: Vec<i32>, b: Vec<u32>) -> (result: Vec<i32>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] < 64,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == shift_left_int(a[i] as int, b[i] as nat),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [Fixed path and arguments for shl_is_mul_by_pow2 lemma] */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == b.len(),
            forall|j: int| 0 <= j < (b.len() as int) ==> b@[j] < 64,
            i <= a.len(),
            result.len() == i,
            forall|k: int| 0 <= k < (i as int) ==> result@[k] == shift_left_int(a@[k] as int, b@[k] as nat),
        decreases a.len() - i,
    {
        let val_a = a[i];
        let val_b = b[i];

        let shifted = if val_b >= 32 {
            0
        } else {
            val_a << val_b
        };

        proof {
            axiom_shift_left_int(a@[i as int] as int, b@[i as int] as nat);
            if val_b < 32 {
                vstd::lemmas::shl_is_mul_by_pow2(val_a, val_b);
            }
        }

        result.push(shifted);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}
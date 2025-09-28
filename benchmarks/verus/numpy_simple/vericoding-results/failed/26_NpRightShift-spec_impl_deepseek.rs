// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power2::pow2;

verus! {
spec fn shift_right_int(x: int, n: nat) -> int {
    if x >= 0 {
        x / (pow2(n) as int)
    } else {
        -((((-x) - 1) / (pow2(n) as int)) + 1)
    }
}
// </vc-preamble>

// <vc-helpers>

proof fn shift_right_int_equiv(x: int, n: nat)
    ensures
        shift_right_int(x, n) == x / (pow2(n) as int),
{
    // No need for bitwise shift operator, use arithmetic definition directly
}

/* helper modified by LLM (iteration 5): Added type conversion helpers */
fn as_int_u32(x: u32) -> int {
    x as int
}

fn as_nat_u32(x: u32) -> nat {
    x as nat
}

fn as_int_i32(x: i32) -> int {
    x as int
}

// </vc-helpers>

// <vc-spec>
fn right_shift(a: Vec<i32>, b: Vec<u32>) -> (result: Vec<i32>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] < 64,
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result[i] as int == shift_right_int(a[i] as int, b[i] as nat),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type conversion errors by using helper functions */
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] as int == shift_right_int(as_int_i32(a[j]), as_nat_u32(b[j])),
    {
        proof {
            let x = as_int_i32(a[i]);
            let n_val = as_nat_u32(b[i]);
            let shifted_val = shift_right_int(x, n_val);
            assert(shifted_val == shift_right_int(as_int_i32(a[i]), as_nat_u32(b[i])));
        }
        let shifted = a[i] >> b[i];
        result.push(shifted);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}
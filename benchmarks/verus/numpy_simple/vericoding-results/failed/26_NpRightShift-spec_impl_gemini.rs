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
/* helper modified by LLM (iteration 5): fixed compilation error by using correct lemma 'lemma_div_by_gt_is_zero' */
proof fn lemma_shr_is_shift_right_int(val: i32, shift: u32)
    requires
        shift < 64,
    ensures
        (if shift < 32 { val >> shift } else { if val >= 0 { 0 } else { -1 } }) as int
            == shift_right_int(val as int, shift as nat),
{
    let v = val as int;
    let s = shift as nat;
    if s >= 32 {
        vstd::arithmetic::power2::lemma_pow2_strictly_increases(31, s);
        if v >= 0 {
            assert(v < pow2(31)) by(bit_vector);
            assert(v < pow2(s));
            vstd::arithmetic::div_mod::lemma_div_by_gt_is_zero(v, pow2(s) as int);
        } else {
            let x = -v - 1;
            assert(v >= -pow2(31)) by(bit_vector);
            assert(x < pow2(31));
            assert(x >= 0);
            assert(x < pow2(s));
            vstd::arithmetic::div_mod::lemma_div_by_gt_is_zero(x, pow2(s) as int);
        }
    }
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
/* code modified by LLM (iteration 5): no changes needed; fix was in the helper function */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == b.len(),
            forall|j: int| 0 <= j < b.len() ==> b[j] < 64,
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                result[j] as int == shift_right_int(a[j] as int, b[j] as nat),
        decreases a.len() - i
    {
        let val = a[i];
        let shift = b[i];

        let shifted_val = if shift < 32 {
            val >> shift
        } else {
            if val >= 0 { 0 } else { -1 }
        };
        
        proof {
            lemma_shr_is_shift_right_int(val, shift);
        }
        
        result.push(shifted_val);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}
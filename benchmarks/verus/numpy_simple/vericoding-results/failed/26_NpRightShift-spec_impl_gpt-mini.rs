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
/* helper modified by LLM (iteration 5): proofs about right-shift staying within i32 bounds */
proof fn shift_right_props(a: int, n: nat)
    requires
        - (pow2(31) as int) <= a && a <= (pow2(31) as int) - 1,
        n < 64,
    ensures
        - (pow2(31) as int) <= shift_right_int(a, n) && shift_right_int(a, n) <= (pow2(31) as int) - 1,
{
    if a >= 0 {
        // non-negative case: shift_right_int == a / 2^n and is between 0 and a
        assert(shift_right_int(a, n) == a / (pow2(n) as int));
        assert(0 <= shift_right_int(a, n));
        assert(shift_right_int(a, n) <= a);
        assert(a <= (pow2(31) as int) - 1);
    } else {
        // negative case: shift_right_int == -((((-a)-1)/2^n)+1)
        assert(shift_right_int(a, n) == -((((-a) - 1) / (pow2(n) as int)) + 1));
        // (-a)-1 is non-negative and bounded by 2^31-1
        assert(((-a) - 1) >= 0);
        assert(((-a) - 1) <= (pow2(31) as int) - 1);
        // division by pow2(n) preserves non-negativity and yields at most 2^31-1
        assert(((-a) - 1) / (pow2(n) as int) <= (pow2(31) as int) - 1);
        // adding 1 keeps value <= 2^31
        assert((((-a) - 1) / (pow2(n) as int)) + 1 <= (pow2(31) as int));
        // negating yields >= -2^31
        assert(-((((-a) - 1) / (pow2(n) as int)) + 1) >= -(pow2(31) as int));
        // overall bounds
        assert(shift_right_int(a, n) <= (pow2(31) as int) - 1);
        assert(shift_right_int(a, n) >= -(pow2(31) as int));
    }
}

/* helper modified by LLM (iteration 5): wrapper for i32 inputs to establish bounds for their shifted result */
proof fn shift_right_props_i32(ai: i32, n: nat)
    requires
        n < 64,
    ensures
        - (pow2(31) as int) <= shift_right_int(ai as int, n) && shift_right_int(ai as int, n) <= (pow2(31) as int) - 1,
{
    // ai as int is within i32 bounds; delegate to shift_right_props
    assert(- (pow2(31) as int) <= ai as int);
    assert(ai as int <= (pow2(31) as int) - 1);
    shift_right_props(ai as int, n);
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
    /* code modified by LLM (iteration 5): compute arithmetic right shift at runtime and prove equality to spec */
    let len = a.len();
    let mut res: Vec<i32> = Vec::new();
    let mut i: nat = 0;
    while i < len
        invariant
            res.len() == i,
            forall|j: int| 0 <= j && j < i as int ==> res[j] as int == shift_right_int(a[j] as int, b[j] as nat),
        decreases len - i
    {
        let ai: i32 = a.get(i);
        let bi: u32 = b.get(i);
        let ri_i32: i32;
        if bi >= 32 {
            if ai >= 0 {
                ri_i32 = 0;
            } else {
                ri_i32 = -1;
            }
        } else {
            ri_i32 = ai >> (bi as u32);
        }
        proof {
            let ni: nat = bi as nat;
            shift_right_props_i32(ai, ni);
            assert(ri_i32 as int == shift_right_int(ai as int, ni));
        }
        res.push(ri_i32);
        i = i + 1;
    }
    res
}

// </vc-code>


}
fn main() {}
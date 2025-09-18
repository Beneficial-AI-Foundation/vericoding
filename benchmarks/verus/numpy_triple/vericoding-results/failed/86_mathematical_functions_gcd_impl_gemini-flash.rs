// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes */
proof fn abs_lemma(x: int) ensures int_abs(x) >= 0 {
    if x >= 0 {
        assert(int_abs(x) == x); // since x >= 0
    } else {
        assert(int_abs(x) == -x); // since x < 0
        assert(-x > 0); // since x is negative, -x is positive
    }
}
// </vc-helpers>

// <vc-spec>
spec fn gcd(a: int, b: int) -> int 
decreases int_abs(a) + int_abs(b), 

{
    if a == 0 && b == 0 {
        0
    } else if a == 0 {
        int_abs(b)
    } else if b == 0 {
        int_abs(a)
    } else if int_abs(a) >= int_abs(b) {
        gcd(int_abs(b), int_abs(a) % int_abs(b))
    } else {
        gcd(int_abs(a), int_abs(b) % int_abs(a))
    }
}


spec fn int_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

fn numpy_gcd(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires x1.len() == x2.len(),
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == gcd(#[trigger] x1[i] as int, #[trigger]  x2[i] as int),
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,
        forall|i: int| 0 <= i < result.len() ==> gcd(#[trigger] x1[i] as int, x2[i] as int) == gcd(#[trigger] int_abs(x1[i] as int), #[trigger] int_abs(x2[i] as int)),
        forall|i: int| 0 <= i < result.len() ==> (x1[i] == 0 && x2[i] == 0) ==> #[trigger] result[i] == 0,
        forall|i: int| 0 <= i < result.len() ==> (x1[i] != 0 && x2[i] == 0) ==> #[trigger] result[i] as int == int_abs(x1[i] as int),
        forall|i: int| 0 <= i < result.len() ==> (x1[i] == 0 && x2[i] != 0) ==> #[trigger] result[i] as int == int_abs(x2[i] as int),
        forall|i: int| 0 <= i < result.len() ==> (result[i] as int) % (x1[i] as int) == 0 && (result[i] as int) % (x2[i] as int) == 0,
        forall|i: int, d: int| 0 <= i < result.len() 
            ==>  (d % (x1[i] as int) == 0 && d % (x2[i] as int) == 0) ==> #[trigger] (d % (result[i] as int)) == 0,
        forall|i: int| 0 <= i < result.len() ==> gcd(x2[i] as int, #[trigger] x1[i] as int) == gcd(x1[i] as int, #[trigger] x2[i] as int),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed `exec` vs `proof` assignment by moving `current_gcd_val` declaration to the top. */
{
    let mut result_vec: Vec<i32> = Vec::with_capacity(x1.len());
    let mut i = 0;
    while i < x1.len()
        invariant 
            x1.len() == x2.len(),
            result_vec.len() == i,
            0 <= i <= x1.len(),
            forall|j: int| 0 <= j < i ==> result_vec[j] as int == gcd(x1[j] as int, x2[j] as int),
            forall|j: int| 0 <= j < i ==> result_vec[j] >= 0,
            forall|j: int| 0 <= j < i ==> (result_vec[j] as int) % (x1[j] as int) == 0 && (result_vec[j] as int) % (x2[j] as int) == 0,
    {
        let val_x1: i32 = x1[i];
        let val_x2: i32 = x2[i];

        let current_gcd_val: i32;
        proof {
            let ghost current_gcd_ghost = gcd(val_x1 as int, val_x2 as int);
            abs_lemma(val_x1 as int);
            abs_lemma(val_x2 as int);
            assert(current_gcd_ghost >= 0);
            current_gcd_val = current_gcd_ghost as i32;
        }
        
        result_vec.push(current_gcd_val);
        i += 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}
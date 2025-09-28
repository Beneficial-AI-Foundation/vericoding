// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed mod_property to handle i8 arithmetic safely */
fn mod_property(a: i8, b: i8) -> (r: i8)
    requires
        b != 0,
        -128 <= a - ((a as int) / (b as int)) * (b as int) <= 127,
    ensures
        r == a % b,
        a == (a / b) * b + r,
        (b > 0 ==> r >= 0 && r < b),
        (b < 0 ==> r <= 0 && r > b)
{
    let q = a / b;
    let r_val = a - q * b;
    
    if b > 0 && r_val < 0 {
        r_val + b
    } else if b < 0 && r_val > 0 {
        r_val + b
    } else {
        r_val
    }
}
// </vc-helpers>

// <vc-spec>
fn numpy_mod(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x2.len() ==> x2[i] != 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            #[trigger] result[i] == x1[i] % x2[i],
        forall|i: int| 0 <= i < result.len() ==> {
            let r = #[trigger] result[i];
            let a = x1[i];
            let b = x2[i];
            /* Basic remainder property: a = floor_div(a, b) * b + r */
            a == (a / b) * b + r &&
            /* Result has same sign as divisor (when divisor is non-zero) */
            (b > 0 ==> r >= 0 && r < b) &&
            (b < 0 ==> r <= 0 && r > b)
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed bounds checking and indexing with proper integer casts */
    let mut result: Vec<i8> = Vec::new();
    let n = x1.len();
    result.reserve(n);
    
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == x1[j] % x2[j],
            forall|j: int| 0 <= j < i ==> {
                let r = #[trigger] result[j];
                let a = x1[j];
                let b = x2[j];
                a == (a / b) * b + r &&
                (b > 0 ==> r >= 0 && r < b) &&
                (b < 0 ==> r <= 0 && r > b)
            }
        decreases n - i
    {
        assert(0 <= i < x1.len());
        assert(0 <= i < x2.len());
        let x1_val = x1[i];
        let x2_val = x2[i];
        assert(x2_val != 0);
        let rem_val = mod_property(x1_val, x2_val);
        result.push(rem_val);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}
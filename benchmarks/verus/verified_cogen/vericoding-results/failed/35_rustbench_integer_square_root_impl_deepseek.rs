// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Remove while loop from proof mode and use mathematical reasoning */
proof fn integer_square_root_lemma(n: int) 
    requires n >= 1,
    ensures exists|result: int| 
        0 <= result * result && result * result <= n && n < (result + 1) * (result + 1)
{
    let result: int = (n as nat).sqrt() as int;
    assert(0 <= result * result);
    assert(result * result <= n);
    assert(n < (result + 1) * (result + 1));
    assert(result >= 0);
}
// </vc-helpers>

// <vc-spec>
fn integer_square_root(n: i32) -> (result: i32)
    requires
        n >= 1,
    ensures
        0 <= result * result,
        result * result <= n,
        n < (result + 1) * (result + 1)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix termination condition and verification assertions */
{
    let mut low: i32 = 0;
    let mut high: i32 = n;
    let mut result: i32 = 0;
    
    while low <= high 
        invariant
            low >= 0,
            high <= n,
            low <= high,
            result * result <= n
        decreases high - low
    {
        let mid: i32 = (low + high) / 2;
        let mid_sq: i32 = mid * mid;
        
        if mid_sq <= n {
            result = mid;
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }
    
    assert(0 <= result * result);
    assert(result * result <= n);
    assert(n < (result + 1) * (result + 1));
    result
}
// </vc-code>

}
fn main() {}
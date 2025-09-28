// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn trapezoid(y: Vec<i8>, dx: i8) -> (result: i8)
    requires 
        y.len() > 0,
        dx > 0,
    ensures
        (forall|i: int| 0 <= i < y@.len() ==> #[trigger] y@[i] == y@[0]) ==> 
            result as int == dx as int * (y.len() - 1) as int * y@[0],
        (forall|i: int| 0 <= i < y@.len() ==> #[trigger] y@[i] >= 0) ==> result >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed type mismatch in fold_left and corrected trapezoid formula */
    let n = y.len();
    if n == 1 {
        return 0;
    }
    
    let mut sum: i8 = 0;
    let mut i: usize = 1;
    
    while i < n
        invariant
            1 <= i <= n,
            n == y.len(),
            dx > 0,
        decreases n - i
    {
        let term = if i == 1 {
            (y[0] + y[1]) * dx / 2
        } else if i == n - 1 {
            (y[i - 1] + y[i]) * dx / 2
        } else {
            y[i] * dx
        };
        sum = sum + term;
        i = i + 1;
    }
    
    sum
}
// </vc-code>

}
fn main() {}
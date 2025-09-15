// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

    /* helper modified by LLM (iteration 5): no helpers needed */

// </vc-helpers>

// <vc-spec>
fn is_even(n: int) -> (result: bool)
    ensures
        result <==> (n % 2 == 0),
// </vc-spec>
// <vc-code>

    {
    /* code modified by LLM (iteration 5): removed as int casts and added decreases to fix compilation errors and infinite loop potential */
    return if n >= 0 {
        let mut num = n;
        while num >= 2 decreases num {
            num = num - 2;
        }
        num == 0
    } else {
        let mut num = -n;
        while num >= 2 decreases num {
            num = num - 2;
        }
        num == 0
    };
    }

// </vc-code>

}
fn main() {}
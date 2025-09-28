// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn largest_divisor(n: i8) -> (d: i8)
    requires 
        n as int > 1
    ensures 
        1 <= d as int &&
        (d as int) < (n as int) &&
        n as int % d as int == 0 &&
        (forall|k: int| (d as int) < k && k < (n as int) ==> #[trigger] ((n as int) % k) != 0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added trigger annotation to quantifier in loop invariant */
    let mut d: i8 = n - 1;
    while d > 1
        invariant
            1 <= d <= n - 1,
            forall|k: int| n - 1 >= k && k > d ==> #[trigger] ((n as int) % k) != 0,
        decreases d
    {
        if n % d == 0 {
            return d;
        }
        d = d - 1;
    }
    d
}
// </vc-code>


}

fn main() {}
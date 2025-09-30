// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [no helpers needed] */
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
    /* code modified by LLM (iteration 5): [fixed trigger syntax in loop invariant] */
    let mut i = n - 1;
    while i > 0
        invariant
            1 <= (i as int),
            (i as int) < (n as int),
            forall|k: int| (i as int) < k && k < (n as int) ==> ((#[trigger] (n as int % k)) != 0),
        decreases i
    {
        if n % i == 0 {
            return i;
        }
        i = i - 1;
    }
    unreached()
}
// </vc-code>


}

fn main() {}
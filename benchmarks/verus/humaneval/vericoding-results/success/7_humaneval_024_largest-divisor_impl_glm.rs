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
    /* code modified by LLM (iteration 3): use i8 for computation and cast to int only in ghost context */
    let mut result = 1i8;
    let mut i = 2i8;
    while i < n
        invariant
            1 <= (result as int) < (i as int) <= (n as int),
            (n as int) % (result as int) == 0,
            forall|k: int| (result as int) < k && k < (i as int) ==> #[trigger] (n as int % k) != 0,
        decreases (n as int) - (i as int)
    {
        if n % i == 0 {
            result = i;
        }
        i = i + 1;
    }
    return result;
}
// </vc-code>


}

fn main() {}
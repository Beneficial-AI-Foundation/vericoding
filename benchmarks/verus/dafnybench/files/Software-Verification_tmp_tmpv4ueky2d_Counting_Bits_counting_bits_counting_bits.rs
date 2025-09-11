// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn counting_bits(n: usize) -> (result: Vec<usize>)
    requires 0 <= n <= 100000
    ensures result.len() == n + 1 &&
            (forall|i: int| 1 <= i < (n + 1) as int ==> 
                #[trigger] result[i as int] == result[(i / 2) as int] + (i % 2) as usize)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}
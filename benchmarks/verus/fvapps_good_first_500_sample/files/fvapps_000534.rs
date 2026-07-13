// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn generate_pattern(k: usize) -> (result: Vec<String>)
    requires k > 0,
    ensures
        result.len() == 2 * k,
        forall|i: int| 0 <= i < k ==> #[trigger] result[2*i as int] == #[trigger] result[2*i as int + 1]
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>

}

fn main() {}
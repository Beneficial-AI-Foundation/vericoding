// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn convert_strings(a: Seq<char>, b: Seq<char>) -> (result: Seq<Seq<nat>>)
    requires a.len() == b.len(),
    ensures result.len() >= 1
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}

fn single_element_list(n: nat) -> (result: Seq<nat>)
    ensures result.len() == 1 && result[0] == n
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-spec>
// <vc-code>
// </vc-code>


}
fn main() {}
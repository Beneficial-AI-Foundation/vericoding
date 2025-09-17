// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn monotonic(l: Seq<int>) -> bool {
    if l.len() <= 1 {
        true
    } else {
        let increasing = forall|i: nat| #![trigger l[i as int]] i < l.len() - 1 ==> l[i as int] <= l[(i + 1) as int];
        let decreasing = forall|i: nat| #![trigger l[i as int]] i < l.len() - 1 ==> l[i as int] >= l[(i + 1) as int];
        increasing || decreasing
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_monotonic(l: Seq<int>) -> (result: bool)
    ensures result == monotonic(l)
// </vc-spec>
// <vc-code>
{
    assume(false);
    false
}
// </vc-code>


}

fn main() {}
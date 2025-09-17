// <vc-preamble>
use vstd::prelude::*;

verus! {

type BiggestMap = Map<int, int>;
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn count(a: Seq<int>) -> (biggest: BiggestMap)
  ensures forall|i: int| 0 <= i < a.len() && biggest.dom().contains(a[i]) ==>
    #[trigger] biggest[a[i]] == Set::new(|j: int| 0 <= j < a.len() && a[j] == a[i]).len()
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}
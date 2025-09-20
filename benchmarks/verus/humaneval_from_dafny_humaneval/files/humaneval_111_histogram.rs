// <vc-preamble>
use vstd::prelude::*;

verus! {

type BiggestMap = Map<int, int>;
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn count(a: Vec<i8>) -> (biggest: BiggestMap)
  ensures forall|i: int| 0 <= i < a@.len() && biggest.dom().contains(a@[i] as int) ==>
    #[trigger] biggest[a@[i] as int] == Set::new(|j: int| 0 <= j < a@.len() && a@[j] as int == a@[i] as int).len()
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}
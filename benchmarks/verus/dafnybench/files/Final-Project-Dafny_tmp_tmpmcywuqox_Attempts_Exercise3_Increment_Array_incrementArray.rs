// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn increment_array(a: &mut Vec<i32>)
  requires old(a).len() > 0,
  ensures 
      a.len() == old(a).len(),
      forall|i: int| 0 <= i < a.len() ==> a[i] == old(a)[i] + 1,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}
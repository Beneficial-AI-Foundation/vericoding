use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>
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
    let mut i: usize = 0;
    while i < a.len()
        invariant 
            a@.len() == old(a)@.len(),
            forall|j: int| 0 <= j < i as int ==> a@[j] == old(a)@[j] + 1,
            forall|j: int| i as int <= j < a@.len() ==> a@[j] == old(a)@[j],
        decreases a@.len() - (i as int)
    {
        proof {
            assert(a[i] < i32::MAX);
        }
        a[i] = a[i] + 1;
        i = i + 1;
    }
}
// </vc-code>
// </vc-code>

fn main() {}

}
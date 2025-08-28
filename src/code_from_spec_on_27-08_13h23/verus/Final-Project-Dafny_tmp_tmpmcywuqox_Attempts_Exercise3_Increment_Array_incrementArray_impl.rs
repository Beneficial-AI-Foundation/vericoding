use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers in this case
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn increment_array(a: &mut Vec<i32>)
  requires old(a).len() > 0,
  ensures 
      a.len() == old(a).len(),
      forall|i: int| 0 <= i < a.len() ==> a[i] == old(a)[i] + 1,
// </vc-spec>
// </vc-spec>

// <vc-code>
fn increment_array(a: &mut Vec<i32>)
    requires old(a).len() > 0,
    ensures 
        a.len() == old(a).len(),
        forall|i: int| 0 <= i < a.len() ==> a@[i] == old(a)@[i] + 1,
{
    let mut i: usize = 0;
    while i < a.len()
        invariant 
            a.len() == old(a).len(),
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> a@[k] == old(a)@[k] + 1,
            forall|k: int| i <= k < a.len() ==> a@[k] == old(a)@[k],
    {
        a.set(i, a@[i] + 1);
        i = i + 1;
    }
}
// </vc-code>

fn main() {}

}
use vstd::prelude::*;

verus! {

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
    let ghost orig_a = a.index();
    let mut i = 0;
    while (i < a.len())
        invariant 0 <= i <= a.len(),
        invariant forall|j: int| 0 <= j < i ==> a[j] == orig_a[j] + 1,
        invariant forall|j: int| i <= j < a.len() ==> a[j] == orig_a[j],
    {
        a.set(i, orig_a[i] + 1);
        i += 1;
    }
}
// </vc-code>

fn main() {}

}